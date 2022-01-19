import requests
import sys
import time

ip = sys.argv[1]
port = sys.argv[2]

time.sleep(10)

for i in range(0, 30):
    try:
      r = requests.get('http://%s:%s/' % (ip, port), timeout = 5)
      print(r.text, flush = True)
    except:
      print("Could not fetch a response", flush = True)
