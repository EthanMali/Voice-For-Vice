"""
VFV (Voice For Vice)
============================

Configuration:
Edit config.ini to change settings:
- PTT_KEY: The keyboard key to hold while speaking (default: shift)
- MODEL_SIZE: Whisper model size (default: small)

"""
import numpy as np
import whisper
import keyboard
import pyautogui
import pyaudio
import wave
import time
import configparser
import os
import pygetwindow as gw
import logging
import re
from thefuzz import process, fuzz
from typing import Optional, List
import ctypes
import io
import torch
from threading import Thread
from scipy import signal  # For audio filtering
from queue import Queue
import json
from fuzzywuzzy import fuzz
import phonetics
from datetime import datetime

# Setup logging
logging.basicConfig(
    filename='vfv.log',
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# Configuration
CONFIG_FILE = "config.ini"
DEFAULT_PTT_KEY = 'shift'
DEFAULT_MODEL_SIZE = 'base'
FASTER_AUDIO_SETTINGS = {
    'format': pyaudio.paInt16,
    'channels': 1,
    'rate': 16000,  # Increased from 8000 for better quality
    'frames_per_buffer': 512,  # Slightly larger buffer
    'input': True,
    }

class VoiceATC:
    def __init__(self):
        self.model = None
        self.audio = None
        self.stream = None
        self.ptt_key, self.model_size = self.load_config()
        self.command_cache = {}
        self.audio_queue = Queue()
        self.load_model()

        #fixes init
        self.airport_code = self.prompt_airport_code()
        self.faa_fixes = self.load_faa_fixes()

        # Add this to your VoiceATC class initialization
        self.command_examples = """
            [EXAMPLE COMMANDS]
            - "Skywest 452, descend and maintain 5000 feet" → ";452 D050"
            - "Delta 123, turn left heading 270" → ";123 l270"
            - "American 456, cleared ILS runway 28L" → ";456 CI28L"
            - "United 789, expect visual approach runway 34R" → ";789 EV34R"
            - "N123AB, maintain 8000 feet" → ";123AB C080"
            - "Southwest 234, contact tower" → ";234 TO"
            - "Jetblue 567, cleared direct JANKE" → ";567 DJANKE"
            - "Westjet 890, reduce speed to 210 knots" → ";890 S210"
            """
        self.command_history = []

        # Initialize all pre-compiled regex patterns
        self.regex_patterns = {
            'runway': re.compile(r'(\d{1,2})([lrc]?)'),
            'altitude': re.compile(r'[\d,]+'),
            'speed': re.compile(r'(?:speed|maintain|reduce|increase)\D*(\d{2,3})\s*knots?'),
            'heading': re.compile(r'heading (\d{2,3})'),
            'ils_expect': re.compile(r'ils runway (\d{1,2})(?:([lrc])|\s+(left|right|center))', re.IGNORECASE),
            'rnav_expect': re.compile(r'rnav runway (\d{1,2})(?:([lrc])|\s+(left|right|center))', re.IGNORECASE),
            'ils_cleared': re.compile(r'ils.*?runway (\d{1,2})(?:([lrc])|\s+(left|right|center))', re.IGNORECASE),
            'rnav_cleared': re.compile(r'rnav.*?runway (\d{1,2})(?:([lrc])|\s+(left|right|center))', re.IGNORECASE),
            }

        # Start processing thread
        self.processing_thread = Thread(target=self.process_audio_queue, daemon=True)
        self.processing_thread.start()

        # Enhanced word replacements dictionary with additions from log analysis
        self.word_replacements = {
            # Improved airline names with more variations
            r'\b(?:sky\s?west|skywest|skw|sky\s?w|sky\s?watch|sky\s?ward|sky\s?wide|sky\s?wire|sky\s?wast|sky\s?ways|sky\s?way|sky\s?lar)\b': 'skywest',
            r'\b(?:west\s?jet|westjet|wj|west\s?j)\b': 'westjet',
            r'\b(?:american|american airlines|aal|america)\b': 'american',
            r'\b(?:delta|delta airlines|dal|delta air)\b': 'delta',
            r'\b(?:united|united airlines|ual|you nighted)\b': 'united',
            r'\b(?:southwest|southwest airlines|swa|south west)\b': 'southwest',
            r'\b(?:jet\s?blue|jetblue|jbu|jet blue|jet\s?b)\b': 'jetblue',
            r'\b(?:envoy|envy|envoi|onvoi|on board)\b': 'envoy',
            r'\b(?:blue\s?streak|blue\s?shriek)\b': 'bluestreak',

            r'\bmount vernon\b': 'mt vernon',
            r'\bmt vernon\b': 'mt vernon',
            r'\bmount v\b': 'mt vernon',
            r'\bmt v\b': 'mt vernon',

            # Enhanced phonetic alphabet with more misrecognitions
            'alpha': 'a', 'alfa': 'a', 'owl fa': 'a', 'alba': 'a',
            'bravo': 'b', 'brah vo': 'b', 'bray vo': 'b', 'bravo': 'b',
            'charlie': 'c', 'char lee': 'c', 'shar lee': 'c', 'charley': 'c',
            'delta': 'd', 'dell ta': 'd', 'dell tuh': 'd', 'della': 'd',
            'echo': 'e', 'eck oh': 'e', 'eh ko': 'e', 'eco': 'e',
            'foxtrot': 'f', 'fox trot': 'f', 'focks trot': 'f', 'fox trot': 'f', 'fox drop':'f', 'foxstap' : 'f',
            'golf': 'g', 'gulf': 'g', 'goal f': 'g', 'gulf': 'g',
            'hotel': 'h', 'hoe tell': 'h', 'ho tell': 'h', 'hotel': 'h',
            'india': 'i', 'in dee ah': 'i', 'in dia': 'i', 'indigo': 'i',
            'juliet': 'j', 'jew lee et': 'j', 'jool yet': 'j', 'juliet': 'j',
            'kilo': 'k', 'key low': 'k', 'kee lo': 'k', 'kilo': 'k',
            'lima': 'l', 'lee ma': 'l', 'lye ma': 'l', 'lima': 'l',
            'mike': 'm', 'my ke': 'm', 'mic': 'm', 'mike': 'm',
            'november': 'n', 'no vem ber': 'n', 'know vem ber': 'n', 'november': 'n',
            'oscar': 'o', 'oss car': 'o', 'aws car': 'o', 'oscar': 'o',
            'papa': 'p', 'pah pah': 'p', 'paw paw': 'p', 'papa': 'p',
            'quebec': 'q', 'kay beck': 'q', 'kweh beck': 'q', 'quebec': 'q',
            'romeo': 'r', 'row me oh': 'r', 'roh me oh': 'r', 'romeo': 'r', 'romio': 'r',
            'sierra': 's', 'see air ah': 's', 'sigh air ah': 's', 'sierra': 's',
            'tango': 't', 'tan go': 't', 'tang oh': 't', 'tango': 't',
            'uniform': 'u', 'you knee form': 'u', 'yoo nee form': 'u', 'uniform': 'u',
            'victor': 'v', 'vic tor': 'v', 'vik tor': 'v', 'victor': 'v',
            'whiskey': 'w', 'wiss key': 'w', 'whis key': 'w', 'whiskey': 'w',
            'xray': 'x', 'ex ray': 'x', 'ecks ray': 'x', 'xray': 'x', 'x-ray': 'x',
            'yankee': 'y', 'yang key': 'y', 'yank ee': 'y', 'yankee': 'y',
            'zulu': 'z', 'zoo loo': 'z', 'zoo lu': 'z', 'zulu': 'z',
            'emir8s' :'emirites',

            # Enhanced numbers with more misrecognitions
            'zero': '0', 'hero': '0', 'hear oh': '0', 'ze ro': '0',
            'one': '1', 'won': '1', 'wan': '1', 'wun': '1',
            'two': '2', 'too': '2', 'true': '2', 'to': '2',
            'three': '3', 'tree': '3', 'threw': '3', 'free': '3', 'through': '3',
            'four': '4', 'for': '4', 'fore': '4', 'fower': '4',
            'five': '5', 'fife': '5', 'fyve': '5', 'fife': '5',
            'six': '6', 'sicks': '6', 'sex': '6', 'sax': '6',
            'seven': '7', 'sebben': '7', 'sven': '7', 'sevin': '7',
            'eight': '8', 'ait': '8', 'ate': '8', 'ait': '8',
            'nine': '9', 'niner': '9', 'nyne': '9', 'niner': '9', '9 or': '9',
            'ten': '10', 'tin': '10', 'tenne': '10', 
            'eleven': '11', 'leven': '11', 'e leven': '11',
            'twelve': '12', 'twelf': '12', 'twelv': '12',
            'thirteen': '13', 'thur teen': '13', 'ter teen': '13',
            'twenty': '20', 'twen ty': '20', 'twunty': '20',
            'thirty': '30', 'thurty': '30', 'dirty': '30',
            'forty': '40', 'for ty': '40', 'farty': '40',
            'fifty': '50', 'fif ty': '50', 'fivety': '50',
            'sixty': '60', 'six ty': '60', 'siksty': '60',
            'seventy': '70', 'seven ty': '70', 'sevendy': '70',
            'eighty': '80', 'eight ty': '80', 'aydee': '80',
            'ninety': '90', 'nine ty': '90', 'nindy': '90',

            # Common command words with more variations
            'maintain': 'maintain', 'man tain': 'maintain', 'men tain': 'maintain', 'main tain': 'maintain',
            'descend': 'descend', 'de scend': 'descend', 'the send': 'descend', 'decent': 'descend',
            'climb': 'climb', 'clime': 'climb', 'cly me': 'climb', 'climb': 'climb',
            'heading': 'heading', 'hed ing': 'heading', 'head in': 'heading', 'head ing': 'heading',
            'speed': 'speed', 'sped': 'speed', 'spee dee': 'speed', 'speed': 'speed',
            'knots': 'knots', 'nauts': 'knots', 'notes': 'knots', 'knots': 'knots',
            'runway': 'runway', 'run way': 'runway', 'r and a': 'runway', 'run way': 'runway',
            'ils': 'ils', 'ill ess': 'ils', 'ill s': 'ils', 'ils': 'ils',
            'visual': 'visual', 'vizh ul': 'visual', 'viz you all': 'visual', 'visual': 'visual',
            'cleared': 'cleared', 'cleard': 'cleared', 'cleer ed': 'cleared', 'cleared': 'cleared',
            'expect': 'expect', 'ex pect': 'expect', 'ex pekt': 'expect', 'expect': 'expect',
            'contact': 'contact', 'con tact': 'contact', 'conn tacked': 'contact', 'contact': 'contact',
            'intercept': 'intercept', 'in ter sept': 'intercept', 'inner sept': 'intercept', 'intercept': 'intercept',
            'localizer': 'localizer', 'low kal izer': 'localizer', 'local ize her': 'localizer', 'localizer': 'localizer',
            'expedite': 'expedite', 'ex pe dite': 'expedite', 'exped ite': 'expedite', 'expedite': 'expedite',
            'fire heading': 'fly heading',  # Fix common misrecognition
            'clte maintain': 'climb and maintain',  # Fix common misrecognition
            'turn lap heading': 'turn left heading',  # Fix common misrecognition
            'expect the ils' : 'expect ils',
            'radar contact': '',
            'claire, direct': 'cleared direct',
            'klamen maintain': 'climb and maintain',
            'the set of maintain' : 'descend and maintain',
            'to set and maintain' : 'descend and maintain',
            'heading': 'fly heading',
            'expect the rnav': 'expect rnav',
            "rnap": "rnav",
            "clear direct": "cleared direct",
            ",": "",
            "intercept the localizer": "intercept localizer",
            "clare": "cleared",
            "claire" : "cleared",
            "klederik": "cleared direct",
            "maintain a": "maintain",
            "-":"",
            "newark approuch" : "",
            "clear 2": "cleared",
            "quiderac" : "cleared direct",
            "onvoice": "envoy",
            "are now": "rnav",
            "our nav": "rnav",
            "rnaw": "rnav",
            "r now": "rnav",
            "common": "climb",
            "realmio" :"r",
            "r9": "rnav",
            "i10t": "ident",
            "derek": "direct",
            "2wer": "tower",
            "mromio": "mr",
            "cleared 2 rnav": "cleared rnav",
            "r and r":"rnav",
            "screen 4":"springfield",
            "cladrack":"cleared direct",
            "remember":"november",
            "claderick": "cleared direct",
            "this regard":"disregard",
            "glair": "clear",
            "clair": "clear",
            'foxtrap': 'f',
            'rnab': 'rnav',
            'glader': 'cleared',
            'rna' : 'rnav',
            'foxrock' : 'f',
            'cleareddrac':'cleared direct',
            'moc c': 'moxy',
            'moxc': 'moxy',
            'on voice': 'envoy',
            'rnavv': 'rnav',
            ' mountain': 'mt',

            
            'themt burn'   : 'mt vernon',
            'po2mac approach': '',
            'cloud remain': 'climb and maintain',
            'amount 4an unveasured': 'mt vernon',
            'amount burn on': 'mt vernon',
            'clamana maintain': 'climb and maintain',
            'mount burn': 'mt vernon',
            'send and maintain': 'descend and maintain',
            'clominant maintain': 'climb and maintain',
            'recard': 'brickyard',
            'them out vernon visual': 'mt vernon visual',
            'them out learn on visual runway 1': 'mt vernon visual runway 1',
            'and receptor': 'intercept',
            'mount run on a': 'mt vernon',
            'themt vernav on the': 'mt vernon',
            'themtvernon': 'mt vernon',
            'them out very nonvisual': 'mt vernon visual',
            'mount run on visual': 'mt vernon visual',
            ' clominimaintain': 'climb and maintain',
            'mount 4 nonvisual': 'mt vernon visual',
            ' them out run on a': 'mt vernon',
            'clamant maintain': 'climb and maintain',
            ' themtvern on visual': 'mt vernon visual',
            'renouts': 'knots',
            'contact potomac approach': 'contact approach',
            'maverine individual approach': 'mt vernon visual',
            'cladwick': 'cleared direct',
            'themtvern on visual': 'mt vernon visual',
            'renouts': 'knots',
            'contact potomac approach': 'contact approach',
            'maverine individual approach': 'mt vernon visual',
            'mount burn on visual': 'mt vernon visual',
            'mount vernon vegl': 'mt vernon visual',
            'mountain vernon visual': 'mt vernon visual',
            'mt burn on visual': 'mt vernon visual',
            'mt vernon vegl': 'mt vernon visual',
            'them out vernon visual': 'mt vernon visual',
            'mount vernon on visual': 'mt vernon visual',
            'mt vernon on visual': 'mt vernon visual',
            'mount vernon visual': 'mt vernon visual',
            'mt vernon visual runway 1': 'mt vernon visual',
            'mt vernon visual runway 1 approach': 'mt vernon visual',
            'mt vernon on a visual runway 1': 'mt vernon visual',
            'the mount vernon visual': 'mt vernon visual',
            'the mt vernon visual': 'mt vernon visual',
            'the mount burn on visual': 'mt vernon visual',
            'themt vernon visual': 'mt vernon visual',
            'themt burn on visual': 'mt vernon visual',
            'the mount run on a visual': 'mt vernon visual',
            'themt vernav on the visual': 'mt vernon visual'       
     }

        # New protected phrases list
        self.protected_phrases = [
            'runway',
            'ils runway',
            'rnav runway',
            'visual approach',
            'skywest',
            'westjet',
            'american',
            'delta',
            'united',
            'southwest',
            'jetblue',
            'contact tower',
            'tam',
            'cleared',
            '40',
            'tower',
            'ident'
        ]

        # Enhanced airline patterns for callsign extraction
        self.airline_patterns = {
            'skywest': r'\b(?:sky\s?west|skw)\s*(\d{2,4})([a-z])?\b',
            'westjet': r'\b(?:west\s?jet|wj)\s*(\d{2,4})([a-z])?\b',
            'american': r'\b(?:american|aal)\s*(\d{2,4})([a-z])?\b',
            'delta': r'\b(?:delta|dal)\s*(\d{2,4})([a-z])?\b',
            'united': r'\b(?:united|ual)\s*(\d{2,4})([a-z])?\b',
            'southwest': r'\b(?:southwest|swa)\s*(\d{2,4})([a-z])?\b',
            'jetblue': r'\b(?:jet\s?blue|jbu)\s*(\d{2,4})([a-z])?\b',
            'alaska': r'\b(?:alaska|asa)\s*(\d{2,4})([a-z])?\b',
            'generic': r'\b([a-z]{2,3})\s*(\d{2,4})([a-z])?\b',
            'envoy': r'\b(?:ENVOY|ENY)\s*(\d{2,4})([A-Z])?\b',
            'commuter': r'\b(?:commut[ae]r\s*air|com\s*air|comm\s*air|comair|cma|cmair)\s*(\d{2,4})([a-z])?\b'
        }
        self.number_words = {
            "zero": "0", "one": "1", "two": "2", "three": "3", "four": "4",
            "five": "5", "six": "6", "seven": "7", "eight": "8", "niner": "9",
            "ten": "10", "eleven": "11", "twelve": "12", "thirteen": "13",
            "fourteen": "14", "fifteen": "15", "sixteen": "16", "seventeen": "17",
            "eighteen": "18", "nineteen": "19", "twenty": "20", "thirty": "30",
            "forty": "40", "fifty": "50", "sixty": "60", "seventy": "70",
            "eighty": "80", "ninety": "90"
        }
        self.phrase_patterns = [
            # Number formatting
            (r'(\d)-(\d)-(\d)-(\d)', r'\1\2\3\4'),  # Convert 8-2-1-0 to 8210
            (r'(\d)-(\d)-(\d)', r'\1\2\3'),        # Convert 3-1-0 to 310
            (r'(\d)-(\d)', r'\1\2'),               # Convert 3-1 to 31
            (r'(\d)\s(\d)\s(\d)', r'\1\2\3'),      # Convert "3 2 0" to "320"
            (r'(\d)\s(\d)', r'\1\2'),              # Convert "3 2" to "32"
            (r'(\d)\.(\d+)', r'\1\2'),             # Convert 43.91 to 4391
            (r'(\d+)\s*,\s*(\d+)', r'\1\2'),       # Convert 4,000 to 4000

            (r'expect (?:the )?mt vernon visual', 'expect mt vernon visual'),
            (r'mt vernon visual runway', 'mt vernon visual runway'),
            
            # Command standardization
            (r'fly heading[s]?', 'heading'),
            (r'clear(?:ed)? to', 'cleared'),
            (r'runway (\d+)\s*([lrc])', r'runway \1\2'),
            (r'descend (?:and )?to maintain', 'descend and maintain'),
            (r'climb (?:and )?to maintain', 'climb and maintain'),
            (r'(\d)\s*([a-z])\b', r'\1\2'),        # Combine numbers with letters (e.g., "981 d" -> "981d")
            (r'(\d+)\s*delta\b', r'\1d'),          # Handle "981 Delta" -> "981d"
            (r'\bby\b', 'fly'),                    # Fix "by heading" -> "fly heading"
            (r'\bif i\b', 'fly'),
            (r'expect ils runwestjetay', 'expect ils runway'),
            (r'sky westjetest', 'skywest'),
            (r'runwestjetay', 'runway'),
            (r'rwy\s*(\d+)', r'runway \1'),
            (r'expect\s*ils', 'expect ils'),
            (r'turn lap heading', 'turn left heading'),
            (r'fire heading', 'fly heading'),
            (r'clte maintain', 'climb and maintain'),
            (r'(\d+)\s*june', r'\1'),  # Fix "4 june 76th" -> "476"
            (r'(\d+)(?:st|nd|rd|th)\b', r'\1'),  # Remove ordinal suffixes
            (r'(\d+)\s*trigger\s*(\d+)', r'\1'),  # Remove trigger numbers
            (r'(\d)\s*([a-z])\s*([a-z])\b', r'\1\2\3'),  # For "252 v i" -> "252vi"
            (r'(\d)([a-z])\s+([a-z])\b', r'\1\2\3'),     # For "252v i" -> "252vi"
        ]

    #--------------------------------------------------------------------------------FAA FIXES

    def prompt_airport_code(self) -> str:
        """Prompt user to enter their airport code and validate it"""
        json_file = 'fixes.json'  # Change to 'fixes.json' if keeping that name
        try:
            with open(json_file, 'r') as f:
                data = json.load(f)
                available_airports = [k for k in data if k != "GENERAL"]
                
                while True:
                    print(f"\nAvailable airports: {', '.join(available_airports)}")
                    print("THIS IS FOR FIXES NOT ALL FIXES ARE IMPLIMENTED\nPlease enter your airport code or just hit enter if your airport is not listed:")
                    code = input("Airport Code: ").strip().upper()
                    
                    if code in data or code == "ALL":
                        return code
                    elif code == "":
                        return None
                    print(f"Invalid code. Please choose from: {', '.join(available_airports)} or ALL")
        
        except FileNotFoundError:
            logger.error(f"FAA fixes file '{json_file}' not found")
            print(f"Error: FAA fixes file '{json_file}' not found. Using ALL fixes only.")
            return "GENERAL"
        except Exception as e:
            logger.error(f"Error reading '{json_file}': {str(e)}")
            print(f"Error reading FAA fixes file: {str(e)}. Using ALL fixes only.")
            return "GENERAL"

    def load_faa_fixes(self):
        """Load FAA fixes with multiple spoken forms"""
        try:
            with open('fixes.json', 'r', encoding='utf-8-sig') as f:
                try:
                    data = json.load(f)
                    fixes = {}
                    
                    # Handle both the specific airport and GENERAL
                    airports_to_load = []
                    if self.airport_code in data:
                        airports_to_load.append(self.airport_code)
                    if "GENERAL" in data:
                        airports_to_load.append("GENERAL")
                    
                    for airport in airports_to_load:
                        for written, spoken in data[airport].items():
                            # Handle both single string and list of variations
                            variations = [spoken] if isinstance(spoken, str) else spoken
                            for variation in variations:
                                # Clean and normalize the variation
                                clean_var = re.sub(r'[^\w\s-]', '', variation.upper()).strip()
                                if clean_var:  # Only add if we have a valid string
                                    fixes[clean_var] = written.upper()
                    
                    return fixes
                    
                except json.JSONDecodeError as e:
                    print(f"JSON decode error at line {e.lineno}, column {e.colno}: {e}")
                    return {}
                    
        except Exception as e:
            logger.error(f"Error loading fixes: {str(e)}")
            print(f"Error loading fixes: {str(e)}")
            return {}

    def create_fix_replacements(self):
        """Create word replacements for FAA fixes"""
        replacements = {}
        if not self.faa_fixes:
            return replacements
            
        logger.info(f"Loading FAA fixes for airport: {self.airport_code}")
        
        for spoken, written in self.faa_fixes.items():
            try:
                # Skip if they're the same (no replacement needed)
                if spoken == written:
                    continue
                    
                # Escape special regex characters
                escaped_spoken = re.escape(spoken.lower())
                
                # Create the pattern - match whole words only
                pattern = r'\b' + escaped_spoken + r'\b'
                
                # Add to replacements
                replacements[pattern] = written.lower()
                logger.debug(f"Added fix replacement: {spoken} -> {written}")
                
            except re.error as e:
                logger.warning(f"Regex error for fix '{spoken}': {str(e)}")
                continue
                
        logger.info(f"Loaded {len(replacements)} FAA fix replacements")
        return replacements

    #-******************************************************************************random inits
    def press_enter_raw(self):
        """Presses the ENTER key using Windows API."""
        KEYEVENTF_KEYUP = 0x0002
        VK_RETURN = 0x0D

        ctypes.windll.user32.keybd_event(VK_RETURN, 0, 0, 0)
        time.sleep(0.05)
        ctypes.windll.user32.keybd_event(VK_RETURN, 0, KEYEVENTF_KEYUP, 0)

    def load_config(self) -> tuple:
        """Load or create configuration with PTT key and model size"""
        config = configparser.ConfigParser()
        
        if os.path.exists(CONFIG_FILE):
            config.read(CONFIG_FILE)
            ptt_key = config.get('settings', 'PTT_KEY', fallback=DEFAULT_PTT_KEY)
            model_size = config.get('settings', 'MODEL_SIZE', fallback=DEFAULT_MODEL_SIZE)
            logger.info(f"Loaded config - PTT key: {ptt_key}, Model size: {model_size}")
        else:
            ptt_key = DEFAULT_PTT_KEY
            model_size = DEFAULT_MODEL_SIZE
            config['settings'] = {
                'PTT_KEY': ptt_key,
                'MODEL_SIZE': model_size
            }
            with open(CONFIG_FILE, 'w') as configfile:
                config.write(configfile)
            logger.info(f"Created new config with default settings")
        
        logger.info(f"Using PTT key: {ptt_key}")
        logger.info(f"Using Whisper model: {model_size}")
        print(f"Using PTT key: {ptt_key}")
        print(f"Using Whisper model: {model_size}")
        return ptt_key, model_size
    
    def setup_audio(self):
        """Initialize optimized audio input stream"""
        try:
            self.audio = pyaudio.PyAudio()
            self.stream = self.audio.open(**FASTER_AUDIO_SETTINGS)
            logger.info("Optimized audio stream initialized")
        except Exception as e:
            logger.error(f"Audio initialization failed: {str(e)}")
            raise

    def load_model(self):
        print("Loading optimized Whisper model...")
        try:
            # Get the directory where the script is located
            script_dir = os.path.dirname(os.path.abspath(__file__))
            
            # Set the device (CUDA if available, otherwise CPU)
            device = "cuda" if torch.cuda.is_available() else "cpu"
            
            if torch.cuda.is_available():
                torch.backends.cudnn.benchmark = True
            
            # Load the model and specify the download location
            self.model = whisper.load_model(
                self.model_size,
                device=device,
                download_root=script_dir  # This ensures the model is downloaded to the script's directory
            )
            print(f"Whisper model loaded successfully on {device}")
            print(f"Model files are located in: {script_dir}")
        except Exception as e:
            logger.error(f"Failed to load Whisper model: {str(e)}")
            raise

    #--------------------------------------------------Vice stuff 

    def find_vice_window(self) -> Optional[gw.Window]:
        """Find the VICE ATC window with retries"""
        max_attempts = 3
        for attempt in range(max_attempts):
            windows = [w for w in gw.getAllWindows() if w.title.lower().startswith("vice:")]
            if windows:
                vice_window = windows[0]
                logger.info(f"Found VICE window: {vice_window.title}")
                return vice_window
            time.sleep(1)
        
        logger.warning("VICE window not found after multiple attempts")
        return None

    def send_to_vice(self, command: str):
        """Send command to VICE ATC window with focus handling"""
        if not command.strip():
            return

        vice_window = self.find_vice_window()
        if not vice_window:
            print("VICE ATC window not found!")
            logger.error("VICE ATC window not found!")
            return

        try:
            # Activate window with retries
            for _ in range(3):
                vice_window.activate()
                time.sleep(0.3)
                if vice_window.isActive:
                    break

            if not vice_window.isActive:
                logger.warning("Failed to activate VICE window")
                return

            # Type the command and press ENTER twice (for reliability)
            # Use Windows API to send the text directly
            for c in command:
                ctypes.windll.user32.SendMessageA(vice_window._hWnd, 0x102, ord(c), 0)
            self.press_enter_raw()

            logger.info(f"Command executed: {command}")

        except Exception as e:
            logger.error(f"Error sending command to VICE: {str(e)}")

    def record_audio(self) -> List[bytes]:
        frames = []
        print("\nRecording... ")
        logger.info("\nRecording... ")
        
        try:
            # Test if microphone is working
            test_audio = self.stream.read(1024, exception_on_overflow=False)
            logger.info(f"Debug: Audio chunk size: {len(test_audio)} bytes")
            
            while keyboard.is_pressed(self.ptt_key):
                data = self.stream.read(1024, exception_on_overflow=False)
                frames.append(data)
                print(".", end='', flush=True)
            
            print("\nStopped recording")
            logger.info("\nStopped recording")
            return frames
        except Exception as e:
            print(f"\nError during recording: {e}")
            logger.error(f"\nError during recording: {e}")
            return []
        
    def transcribe_audio(self, frames: List[bytes]) -> Optional[str]:
        if not frames or len(frames) < 10:
            print("Error: No audio frames or too short.")
            logger.error("Error: No audio frames or too short.")
            return None

        try:
            audio_data = b''.join(frames)
            
            # DEBUG: Save audio to a file for playback
            with wave.open("debug_recording.wav", "wb") as wf:
                wf.setnchannels(1)
                wf.setsampwidth(2)  # 16-bit audio
                wf.setframerate(16000)
                wf.writeframes(audio_data)
            logger.info("Saved audio to 'debug_recording.wav'")  # Check this file in a media player
            
            # Convert to numpy array and apply amplification
            audio_array = np.frombuffer(audio_data, dtype=np.int16).astype(np.float32) / 32768.0
            
            audio_array *= 3.0
            audio_array = self.filter_audio(audio_array)
            audio_array = np.clip(audio_array, -1.0, 1.0)
            audio_array = audio_array.astype(np.float32)  # <-- Fix the dtype mismatch

            
            # Debug: Print the average amplitude
            avg_amplitude = np.abs(audio_array).mean()
            logger.info(f"Debug: Audio mean amplitude = {avg_amplitude:.4f}")
            
            # Check if audio is silent (with more lenient threshold)
            if avg_amplitude < 0.02:  # Increased threshold from 0.01
                print(f"Warning: Audio is too quiet (amplitude = {avg_amplitude:.4f})")
                return None
                
            result = self.model.transcribe(
                audio_array,
                language='en',
                fp16=False,
                temperature=0.0,
                beam_size=1,
                initial_prompt="Aircraft radio transmissions using ATC phrases like descend and maintain, heading, expect ILS runway"

            )

            audio_array = self.filter_audio(audio_array)

            
            text = result.get("text", "").strip()
            text = self.preprocess_text(text)

            logger.info(f"Raw Whisper output: '{text}'")  # Debug transcription
            
            if not text or text.isdigit() or len(text) < 3:
                print("Warning: Whisper returned empty or invalid text.")
                return None
                
            return text
            
        except Exception as e:
            print(f"Transcription error: {e}")
            return None
    
    def filter_audio(self, audio_array: np.ndarray) -> np.ndarray:
        """Apply basic audio filtering to improve quality"""
        try:
            # Simple high-pass filter to remove low-frequency noise
            from scipy import signal
            sos = signal.butter(4, 100, 'hp', fs=FASTER_AUDIO_SETTINGS['rate'], output='sos')
            filtered = signal.sosfilt(sos, audio_array)
            return filtered
        except ImportError:
            return audio_array  # Fallback if scipy not available
                
    def process_audio_queue(self):
        """Background thread to process audio chunks"""
        print("Background processing thread started.")
        while True:
            frames = self.audio_queue.get()
            print(f"Processing {len(frames)} audio frames...")
            text = self.transcribe_audio(frames)
            if text:
                print(f"Transcribed text: {text}")
                command = self.format_command(text)
                if command:
                    print(f"Formatted command: {command}")
                    self.send_to_vice(command)

    def preprocess_text(self, text: str) -> str:
        """Enhanced text preprocessing with multi-stage correction"""
        if not text:
            return ""

        # Convert to lowercase and remove special characters (except ,.-)
        text = text.lower()
        text = re.sub(r'[^\w\s,.-]', '', text)
        
        # Stage 1: Protect critical phrases from modification
        protected = {}
        for i, phrase in enumerate(self.protected_phrases):
            placeholder = f'__PROTECTED_{i}__'
            protected[placeholder] = phrase
            text = text.replace(phrase, placeholder)
        
        # Stage 2: Apply word replacements with regex patterns
        for pattern, replacement in self.word_replacements.items():
            text = re.sub(pattern, replacement, text)
        
        # Stage 3: Apply phrase patterns for common multi-word patterns
        for pattern, replacement in self.phrase_patterns:
            text = re.sub(pattern, replacement, text)
        
        # Stage 4: Restore protected phrases
        for placeholder, phrase in protected.items():
            text = text.replace(placeholder, phrase)
        
        # Stage 5: Final cleanup
        text = re.sub(r'\s+', ' ', text).strip()
        text = re.sub(r'\b(\d)\s+(\d)\s+(\d)\b', r'\1\2\3', text)  # Fix spaced numbers
        
        return text
            
    def extract_callsign(self, text: str) -> str:
        """Enhanced callsign extraction with GA support and altitude protection"""
        # Normalize text - uppercase and remove problematic characters
        clean_text = re.sub(r'[^A-Z0-9 ]', '', text.upper())
        
        # Priority 1: GA Aircraft (N-numbers)
        # Matches N123, N123A, N123AB, N1234, N12345, N1234A, etc.
        n_pattern = r'\bN\s*([A-Z]?\d{1,5}[A-Z]{0,2})\b'
        match = re.search(n_pattern, clean_text)
        if match:
            return f"N{match.group(1)}"  # Return full N-number
        
        # Priority 2: Airline callsigns (SOUTHWEST 152)
        airline_pattern = r'\b(SOUTHWEST|SWA|AMERICAN|AAL|DELTA|DAL|UNITED|UAL|JETBLUE|JBU|SKYWEST|SKW|WESTJET|WJ|ENVOY|ENY)\s+(\d{2,4})([A-Z])?\b'
        match = re.search(airline_pattern, clean_text)
        if match:
            flight_num = match.group(2)
            suffix = match.group(3) or ''
            return f"{flight_num}{suffix}"
        
        # Priority 3: Standalone flight numbers (avoiding altitudes)
        # Doesn't match if followed by "thousand", "feet", or runway designators
        standalone_pattern = r'\b(\d{2,4})\b(?!\s*(?:THOUSAND|FEET|FT|[LRC]\b))'
        match = re.search(standalone_pattern, clean_text)
        if match:
            return match.group(1)
        
        # Priority 4: Military/GA callsigns (no airline prefix)
        # Matches patterns like "HALO 01", "REACH 234", "N123AB"
        mil_ga_pattern = r'\b([A-Z]{2,5})\s*(\d{2,4})([A-Z])?\b'
        match = re.search(mil_ga_pattern, clean_text)
        if match:
            prefix = match.group(1)
            number = match.group(2)
            suffix = match.group(3) or ''
            return f"{prefix}{number}{suffix}"
        
        # Final fallback - return empty rather than wrong value
        return ""

    def _extract_airline_callsign(self, text: str) -> str:
        """Enhanced airline callsign extraction with better pattern matching"""
        # Normalize text - uppercase and remove problematic characters
        text = text.upper().replace("-", " ").replace(",", "").replace(".", "")
        
        # Extract first 4 words max (to capture longer airline names)
        first_part = ' '.join(text.split()[:4])
        
        airline_patterns = [
            # Major US Carriers
            r'^(SKY\s?WEST|SKW)\s*(\d{2,4})([A-Z])?\b',
            r'^(WESTJET|WJ)\s*(\d{2,4})([A-Z])?\b',
            r'^(AMERICAN|AAL)\s*(\d{2,4})([A-Z])?\b',
            r'^(DELTA|DAL)\s*(\d{2,4})([A-Z])?\b',
            r'^(UNITED|UAL)\s*(\d{2,4})([A-Z])?\b',
            r'^(SOUTHWEST|SWA)\s*(\d{2,4})([A-Z])?\b',
            r'^(JETBLUE|JBU)\s*(\d{2,4})([A-Z])?\b',
            r'^(ALASKA|ASA)\s*(\d{2,4})([A-Z])?\b',
            r'^(FRONTIER|FFT)\s*(\d{2,4})([A-Z])?\b',
            r'^(SPIRIT|NKS)\s*(\d{2,4})([A-Z])?\b',
            r'^(HAWAIIAN|HAL)\s*(\d{2,4})([A-Z])?\b',
            r'^(MOXY|MXY)\s*(\d{2,4})([A-Z])?\b',

            # US Regionals
            r'^(ENVOY|ENY)\s*(\d{2,4})([A-Z])?\b',
            r'^(ENDEAVOR|EDV)\s*(\d{2,4})([A-Z])?\b',
            r'^(PSA|JIA)\s*(\d{2,4})([A-Z])?\b',
            r'^(PIEDMONT|PDT)\s*(\d{2,4})([A-Z])?\b',
            r'^(REPUBLIC|RPA)\s*(\d{2,4})([A-Z])?\b',
            r'^(MESA|ASH)\s*(\d{2,4})([A-Z])?\b',
            r'^(GOJET|GJS)\s*(\d{2,4})([A-Z])?\b',
            r'^(SILVER|VOI)\s*(\d{2,4})([A-Z])?\b',
            r'^(EXPRESSJET|ASQ)\s*(\d{2,4})([A-Z])?\b',
            r'^(COMMUTAIR|UCA)\s*(\d{2,4})([A-Z])?\b',
            
            # Major International
            r'^(AIR\s?CANADA|ACA)\s*(\d{2,4})([A-Z])?\b',
            r'^(LUFTHANSA|DLH)\s*(\d{2,4})([A-Z])?\b',
            r'^(BRITISH\s?AIRWAYS|BAW)\s*(\d{2,4})([A-Z])?\b',
            r'^(AIR\s?FRANCE|AFR)\s*(\d{2,4})([A-Z])?\b',
            r'^(EMIRATES|UAE)\s*(\d{2,4})([A-Z])?\b',
            r'^(QATAR|QTR)\s*(\d{2,4})([A-Z])?\b',
            r'^(CATHAY|CPA)\s*(\d{2,4})([A-Z])?\b',
            r'^(SINGAPORE|SIA)\s*(\d{2,4})([A-Z])?\b',
            r'^(JAPAN|JAL)\s*(\d{2,4})([A-Z])?\b',
            r'^(ANA|ALL\s?NIPPON)\s*(\d{2,4})([A-Z])?\b',
            
            # Cargo Carriers
            r'^(FEDEX|FDX)\s*(\d{2,4})([A-Z])?\b',
            r'^(UPS|UPS)\s*(\d{2,4})([A-Z])?\b',
            r'^(ATLAS|GTI)\s*(\d{2,4})([A-Z])?\b',
            r'^(KALITTA|CKS)\s*(\d{2,4})([A-Z])?\b',
            r'^(POLAR|PAC)\s*(\d{2,4})([A-Z])?\b',
            r'^(SOUTHERN|SOO)\s*(\d{2,4})([A-Z])?\b',
            
            # Common Charters
            r'^(SUN\s?COUNTRY|SCX)\s*(\d{2,4})([A-Z])?\b',
            r'^(ALLEGIANT|AAY)\s*(\d{2,4})([A-Z])?\b',
            r'^(FRONTIER|FFT)\s*(\d{2,4})([A-Z])?\b',
            r'^(SPIRIT|NKS)\s*(\d{2,4})([A-Z])?\b',
            r'^(DELTA\s?PRIVATE|DJE)\s*(\d{2,4})([A-Z])?\b',
            
            # Military/Government
            r'^(REACH|RCH)\s*(\d{2,4})([A-Z])?\b',
            r'^(OMEGA|OMA)\s*(\d{2,4})([A-Z])?\b',
            r'^(PATRIOT|EJM)\s*(\d{2,4})([A-Z])?\b',
            r'^(NAVY|NJE)\s*(\d{2,4})([A-Z])?\b',
            
            # Generic pattern 
            r'^([A-Z]{2,3})\s*(\d{2,4})\s*([A-Z])?\b'  # Added \s* before suffix

            # And add this special case before the generic pattern:
            r'^(\d{2,4})\s*([A-Z])\s*([A-Z])\b'  # For cases like "252 v i"
        ]
        for pattern in airline_patterns:
                match = re.search(pattern, first_part)
                if match:
                    # Return flight number + optional suffix
                    flight_num = match.group(2)
                    suffix = match.group(3) or ''
                    return f"{flight_num}{suffix}"
            
        # Final fallback - look for any number sequence (including single digits)
        fallback = re.search(r'\b(\d{1,4})([A-Z])?\b', text)
        return f"{fallback.group(1)}{fallback.group(2) or ''}" if fallback else ""
    
    def extract_runway(self, text: str) -> str:
        """Extract runway with designator (e.g., '36L')"""
        match = re.search(r'(\d{1,2})([lrc]?)', text.lower())
        if match:
            runway, designator = match.groups()

            return f"{runway}{designator}" if designator else runway
        return ""
            
    def format_altitude_for_vice(self, alt_str: str) -> str:
        """Convert altitude string to VICE format (e.g., 16000 -> 160, 7000 -> 070)"""
        if not alt_str:
            return "000"
        
        try:
            # Remove any non-digit characters and convert to integer
            clean_num = int(re.sub(r'[^\d]', '', alt_str))
            
            # Special case for numbers like "15" meaning 15000
            if clean_num < 100:
                clean_num *= 1000
                
            # Convert feet to hundreds of feet
            hundreds = clean_num // 100
            
            # Format as 3 digits with leading zeros
            return f"{hundreds:03d}"
        except (ValueError, TypeError):
            return "000"
            
    def extract_direct_fix(self, text: str) -> Optional[str]:
        """AI-powered fix matching for both 'cleared direct' and 'proceed direct'"""
        match = re.search(r'(?:cleared|proceed) direct (\w+(?:\s+\w+)*)', text, re.IGNORECASE)
        if not match:
            return None
        
        spoken_fix = match.group(1).upper().strip()
        logger.info(f"Attempting to match fix: {spoken_fix}")

        # Get all possible fixes
        all_fixes = self.get_all_fix_variations()
        if not all_fixes:
            print("⚠️ No fixes loaded in database")
            return None

        # Try exact match first
        for written, spoken_list in all_fixes.items():
            if spoken_fix in [s.upper() for s in spoken_list] or spoken_fix == written:
                return written

        # Try fuzzy matching
        all_possible = []
        for written, spoken_list in all_fixes.items():
            all_possible.extend(spoken_list)
            all_possible.append(written)
        
        best_match, score = process.extractOne(
            spoken_fix,
            all_possible,
            scorer=fuzz.token_set_ratio,
            score_cutoff=70
        )
        
        if score >= 70:
            for written, spoken_list in all_fixes.items():
                if best_match in spoken_list or best_match == written:
                    return written

        # Try phonetic matching
        spoken_meta = phonetics.metaphone(spoken_fix)
        for written, spoken_list in all_fixes.items():
            for variation in spoken_list + [written]:
                if phonetics.metaphone(variation) == spoken_meta:
                    return written

        print(f"⚠️ No match for '{spoken_fix}'. Similar fixes: {list(all_fixes.keys())[:5]}")
        return None

    def get_all_fix_variations(self):
        """Return all fix variations grouped by written form"""
        variations = {}
        try:
            with open('fixes.json', 'r') as f:
                data = json.load(f)
                for airport in [self.airport_code, "GENERAL"]:
                    if airport in data:
                        for written, spoken in data[airport].items():
                            variations[written] = [spoken] if isinstance(spoken, str) else spoken
        except Exception as e:
            logger.error(f"Error loading fix variations: {str(e)}")
        return variations
      
    def extract_altitude(self, text: str) -> str:
        """Altitude extraction that explicitly avoids callsign numbers and headings"""
        # First get callsign to exclude it from altitude search
        callsign = self.extract_callsign(text)
        protected_text = text.upper().replace(callsign, '') if callsign else text.upper()
        
        # Remove heading numbers first to avoid confusion
        protected_text = re.sub(r'heading \d{2,3}', '', protected_text, flags=re.IGNORECASE)
        
        # Look for altitude patterns
        patterns = [
            r'(?:descend|climb|maintain)\D*(\d+)\s*(?:thousand|k)\b',
            r'(?:altitude|level)\D*(\d[\d,]*)\s*(?:feet|ft)\b',
            r'\b(\d{3,5})\b(?!\s*[A-Z])'  # Numbers not followed by letters
        ]
        
        for pattern in patterns:
            match = re.search(pattern, protected_text)
            if match:
                return match.group(1).replace(',', '')
        
 
    def _match_runway(self, text: str):
        """
        Return (number, designator) or (None, None) if not found.
        • Accepts:
            - "... runway 2", "... runway 22L", "... runway 04 right"
            - "22L" / "04R" / "15C" when 'runway' is omitted
        • Ignores digits that are part of callsigns or altitudes.
        """
        # ❶ First, require the literal word 'runway' if it’s in the phrase
        m = re.search(
            r'runway\s+(\d{1,2})\b(?:\s*(left|right|center)|\s*([lrc]))?',
            text, re.I)
        if m:
            num   = m.group(1)
            side  = (m.group(2) or m.group(3) or '').strip()
            side  = side[0].upper() if side else ''
            return num, side

        # ❷ Otherwise look for the compact form 22L / 15C, but insist on a side
        m = re.search(r'\b(\d{1,2})([lrc])\b', text, re.I)
        if m:
            return m.group(1), m.group(2).upper()

        return None, None


    
    def format_command(self, text):
        if not text:
            return None
        
            
        processed_text = self.preprocess_text(text)

        # Extract callsign
        callsign = self.extract_callsign(processed_text)
        if not callsign:
            print("No valid callsign found")
            return None
        print(f"Extracted callsign: {callsign}")

        cmds = []

        # 1. Altitude Commands (descend/climb/maintain)
        if any(x in processed_text for x in ["descend", "descend and maintain", "climb", "maintain altitude", "climb and maintain"]):
            alt = self.extract_altitude(processed_text)
            if alt:
                formatted_alt = self.format_altitude_for_vice(alt)
                if "descend" in processed_text:
                    if "expedite descent" in processed_text or "expedite" in processed_text:
                        cmds.append("ED")
                    else:
                        cmds.append(f"D{formatted_alt}")
                elif any(x in processed_text for x in ["climb", "climb and maintain"]):
                    if "expedite climb" in processed_text or "expedite" in processed_text:
                        cmds.append("EC")
                    else:
                        cmds.append(f"C{formatted_alt}")  # This was missing in your original code
   
        # 2. HEADING Commands (including turn left/right)
        if "heading" in processed_text:
            # Check for turn directions first
            turn_dir = None
            if "turn right heading" in processed_text:
                turn_dir = "r"
            elif "turn left heading" in processed_text:
                turn_dir = "l"
            
            # First try strict 3-digit match
            match = re.search(r"heading (\d)(\d)(\d)\b", processed_text)
            if not match:
                # Fallback to any 2-3 digit number
                match = re.search(r"heading (\d{2,3})\b", processed_text)
            
            if match:
                if len(match.groups()) == 3:  # Got three separate digits
                    heading = f"{match.group(1)}{match.group(2)}{match.group(3)}"
                else:  # Got combined number
                    heading = match.group(1).ljust(3, '0')[:3]  # Pad with zeros if needed
                
                try:
                    heading_num = int(heading)
                    if 1 <= heading_num <= 360:  # Validate heading range
                        if turn_dir:
                            cmds.append(f"{turn_dir}{heading_num:03d}")  # Turn command (r150/l360)
                        else:
                            cmds.append(f"H{heading_num:03d}")  # Regular heading command
                except ValueError:
                    pass

        # 3. Speed Commands
        if any(x in processed_text for x in ["speed", "knots", "maintain speed", "reduce speed to", "increase speed to"]):
            match = re.search(r'(\d{2,3})\s*knots?|\bspeed\s+(\d{2,3})\b', processed_text)
            if match:
                speed = match.group(1) or match.group(2)
                cmds.append(f"S{speed}")
            elif "say speed" in processed_text:
                cmds.append("SS")  # Say speed command

        # 4. Contact Commands
        if "contact" in processed_text:
            if "tower" in processed_text:
                cmds.append("TO")
            elif "center" in processed_text or "approach" in processed_text or "departure" in processed_text:
                cmds.append("FC")

        # Special Visual Approaches (before the general approach handling)
        visual_approaches = {
            'mt vernon': 'MTV',
            'river': 'RIV'
        }

        # Check both expect and cleared versions
        for approach, code in visual_approaches.items():
            # Check for EXPECT visual approaches
            if (approach in processed_text.lower() and 
                'visual' in processed_text.lower() and
                any(rwy in processed_text.lower() for rwy in ["runway 1", "rwy 1", "runway one"]) and
                'expect' in processed_text.lower()):
                cmds.append(f"E{code}")
                break
            
            # Check for CLEARED visual approaches
            if (approach in processed_text.lower() and 
                'visual' in processed_text.lower() and
                any(rwy in processed_text.lower() for rwy in ["runway 1", "rwy 1", "runway one"]) and
                'cleared' in processed_text.lower()):
                cmds.append(f"C{code}")  # Note the C prefix instead of E
                break

       # 5. Approach Types
        approach_types = {
            'ils': 'I',
            'rnav': 'R',
            'visual': 'V'
        }

        for approach, prefix in approach_types.items():
            # Expect commands
            # --- inside the EXPECT branch ---
            if f"expect {approach}" in processed_text.lower():
                num, side = self._match_runway(processed_text)
                if num:
                    rwy = f"{num[-1]}{side}" if side else num
                    cmds.append(f"E{prefix}{rwy}")
             

                # Special cases (keep existing)
                if ("mt vernon visual" in processed_text.lower() or 
                    "mount vernon visual" in processed_text.lower()) and \
                any(rwy in processed_text.lower() for rwy in ["runway 1", "rwy 1", "runway one"]):
                    cmds.append("EMTV")
                if f"expect the river visual runway 19" in processed_text.lower():
                    cmds.append("ERIV")

            # Cleared commands (same fix as above)
            if f"cleared {approach}" in processed_text.lower():
                num, side = self._match_runway(processed_text)
                if num:
                    rwy = f"{num[-1]}{side}" if side else num
                    cmds.append(f"C{prefix}{rwy}")



        # Enhanced Direct Clearance
        if "cleared direct" in processed_text.lower() or "proceed direct" in processed_text.lower():
            try:
                fix = self.extract_direct_fix(processed_text)
                if fix:
                    cmds.append(f"D{fix}")
                    #print(f" Matched fix: {fix}")
                else:
                    # Show suggestions without crashing
                    match = re.search(r'(?:cleared|proceed) direct (\w+(?:\s+\w+)*)', processed_text, re.IGNORECASE)
                    if match:
                        spoken_fix = match.group(1).upper()
                        all_fixes = []
                        fix_variations = self.get_all_fix_variations()
                        if fix_variations:  # Only proceed if we have fixes loaded
                            for written, spoken_list in fix_variations.items():
                                all_fixes.extend(spoken_list)
                                all_fixes.append(written)
                            
                            print(f"Couldn't find fix '{spoken_fix}'. Did you mean one of these?")
                            suggestions = process.extract(spoken_fix, all_fixes, scorer=fuzz.token_set_ratio, limit=5)
                            for fix, score in suggestions:
                                if score > 50:
                                    print(f" - {fix} (similarity: {score}%)")
                    
                    # Instead of returning None, just skip this command but continue processing others
                    print("Skipping direct clearance due to unknown fix")
            
            except Exception as e:
                logger.error(f"Error processing direct clearance: {str(e)}")
                print(f"Error processing direct clearance, continuing with other commands")
                # Continue with other commands instead of returning None

        # 6. Special Commands
        if "intercept localizer" in processed_text:
            cmds.append("I")
        if "cancel approach clearance" in processed_text.lower():
            cmds.append("CAC")
        if "climb via sid" in processed_text.lower() or "climb via the sid" in processed_text.lower():
            cmds.append("CVS")
        if "ident" in processed_text.lower():
            cmds.append("ID")
        if "cancel speed restriction" in processed_text.lower() or "resume normal speed" in processed_text.lower():
            cmds.append("S")
        if "say present heading" in processed_text.lower() or "what's your heading" in processed_text.lower():
            cmds.append("SH")
        if "squawk" in processed_text.lower():
            match = re.search(r'squawk\s*(\d{4})', processed_text, re.IGNORECASE)
            if match:
                squawk_code = match.group(1)
                cmds.append(f"SQ{squawk_code}")
        if "Resume own navigation" in processed_text.lower():
            cmds.append("RON")

            
        if "disregard" in processed_text.lower() or "cancel" in processed_text.lower():
            print("Disregard command received")
            return None

        if cmds:
            vice_command = f";{callsign} " + " ".join(cmds)
            print(f"[DEBUG] Generated VICE command: {vice_command}")
            return vice_command
        
        print("[DEBUG] No valid commands generated")
        return None
    
    def cleanup(self):
        """Clean up resources"""
        if self.stream:
            self.stream.stop_stream()
            self.stream.close()
        if self.audio:
            self.audio.terminate()
        logger.info("Audio resources released")

    def run(self):
        """Main execution loop with parallel processing"""
        print("\nVoice ATC Controller - Ready (Optimized)")
        print(f"Press and hold '{self.ptt_key}' to speak commands\n")
        
        try:
            self.setup_audio()
            
            while True:
                keyboard.wait(self.ptt_key)
                frames = self.record_audio()
                
                if frames:
                    # Put frames in queue for background processing
                    self.audio_queue.put(frames)
        
        except KeyboardInterrupt:
            print("\nExiting...")
        finally:
            self.cleanup()
            
def main():
    try:
        print(__doc__)  # Print the README at startup
        controller = VoiceATC()
        print(f"\nVFV initialized for airport: {controller.airport_code}")
        controller.run()
    except Exception as e:
        logger.critical(f"Fatal error: {str(e)}")
        print(f"Error: {str(e)}")
   
if __name__ == "__main__":
    main()