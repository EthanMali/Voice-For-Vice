@echo off
cd /d %~dp0
start cmd /k "py -3.12 -m pip install git+https://github.com/openai/whisper.git"
