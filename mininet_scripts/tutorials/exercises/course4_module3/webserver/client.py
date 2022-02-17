import requests
import sys
import time

ip = sys.argv[1]
port = sys.argv[2]
grp_size = int(sys.argv[3])
sleep_time = float(sys.argv[4])
grp_cnt = int(sys.argv[5])

#ok = 0
#not_ok = 0
#time_sum = 0

for i in range(0, grp_cnt):
    for j in range(0, grp_size):
      try:
        start = time.time()
        r = requests.get('http://%s:%s/' % (ip, port), timeout = 5)
        latency = time.time() - start
        print(f"{start} {latency} 1", flush = True)
      except:
        print(f"{start} 5 0", flush = True)

      #print(f"{time_sum} {ok} {not_ok}", flush = True)

    time.sleep(sleep_time)

