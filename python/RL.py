import leanclient as lc
import torch
import json
PROJECT_PATH = "/Users/nelsmartin/Lean/RL"
client = lc.LeanLSPClient(PROJECT_PATH)

file_path = "RL/RLTest.lean"
sfc = client.create_file_client(file_path)
sfc.open_file()
# return 
def get_goal():
    
    # print(sfc.get_file_content())
    print(sfc.get_goal(line=1, character=1))
    print(sfc.get_declarations(line=1, character=1))
    print(sfc.get_diagnostics().diagnostics)

def get_ldecls():
    message = sfc.get_diagnostics().diagnostics[0]['message']
    message = json.loads(message)
    print(type(message[0]))
get_ldecls()