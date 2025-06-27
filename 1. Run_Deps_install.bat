@echo off
cd /d %~dp0
start cmd /k "py -3.12 -m pip install -r requirements.txt"
