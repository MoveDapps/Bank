import subprocess
import json

def process_json(input):
    try:
        output = subprocess.check_output(input.split())
    except Exception as e:
        print(str(e))

    return json.loads(output)

RED='\033[0;31m'
NC='\033[0m'

output=process_json("sui client gas --json")
#print(output)
total_gas = 0
for gas in output:
    total_gas += int(gas['balance']['value'])

print(f"{RED}My SUI coins available...{total_gas} {NC}")
