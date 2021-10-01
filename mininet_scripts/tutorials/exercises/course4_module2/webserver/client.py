import requests
import sys

ip = sys.argv[1]
port = sys.argv[2]

for i in range(1, 50):
    try:
      r = requests.get('http://%s:%s/' % (ip, port), timeout = 5)
      print(r.text)
    except:
      print("Could not fetch a response")
