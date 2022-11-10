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

print(f"{RED}Building package....{NC}")
subprocess.call(["sui", "move", "build"])

print(f"{RED}Runing tests....{NC}")
subprocess.call(["sui", "move", "test"])

print(f"{RED}Deploying package....{NC}")

output=process_json("sui client publish --path . --gas-budget 30000 --json")
PACKAGE=output['effects']['created'][0]['reference']['objectId']

print(f"{RED}Pakcage ID = {NC} {PACKAGE}")

output=process_json(f"sui client call --package {PACKAGE} --module market --function create_pool --gas-budget 30000 --json")
MARKET=output[1]['created'][0]['reference']['objectId']
print(f"{RED}Market ID = {NC} {MARKET}")

output=process_json(f"sui client call --package {PACKAGE} --module market --function create_sub_market --gas-budget 30000 --args {MARKET} --type-args 0x2::sui::SUI --json")
SUI_SUBMARKET=output[1]['created'][1]['reference']['objectId']
print(f"{RED}SUI Market ID = {NC} {SUI_SUBMARKET}")

output=process_json(f"sui client call --package {PACKAGE} --module market --function create_sub_market --gas-budget 30000 --args {MARKET} --type-args {PACKAGE}::fake_usdc::USDC --json")

USDC_SUBMARKET = ''
for created in output[1]['created']:
    if(created['owner']['ObjectOwner'] == MARKET):
        continue
    USDC_SUBMARKET = created['reference']['objectId']

print(f"{RED}USDC Market ID = {NC} {USDC_SUBMARKET}")
