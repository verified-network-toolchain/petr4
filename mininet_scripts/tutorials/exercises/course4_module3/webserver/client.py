import requests
import sys
import time

ip = sys.argv[1]
port = sys.argv[2]
cnt = int(sys.argv[3])

#time.sleep(10)

ok = 0
not_ok = 0
time_sum = 0

for i in range(0, cnt):
    try:
      start = time.time()
      r = requests.get('http://%s:%s/' % (ip, port), timeout = 5)
      latency = time.time() - start
      time_sum += latency
      ok += 1
      #print(r.text, flush = True)
    except:
      not_ok += 1
      #print("Could not fetch a response", flush = True)

print(f"{time_sum} {ok} {not_ok}")
