import requests
import sys

ip = sys.argv[1]
port = sys.argv[2]
r = requests.get('http://%s:%s/' % (ip, port))
print(r.text)
