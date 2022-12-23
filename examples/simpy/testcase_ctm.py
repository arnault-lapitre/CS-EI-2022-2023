import json
import time
from z3 import *


with open('examples/simpy/testcase_ctm.json') as json_data:
   testcase = json.load(json_data)

pretty_str = json.dumps(testcase, indent=2)
print(f"testcase = {pretty_str}")
