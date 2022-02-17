# An trivial application that does nothing
from petr4 import App
from topo import *
from petr4.runtime import *
from tornado.ioloop import *
import sys
import signal

class MyApp(App):
  def init_topo(self):
    topo = Topology()
    
    for i in range(1, 4):
      topo.add_switch("s" + str(i))

    for i in range(1, 5):
      topo.add_host("h" + str(i))

    for i in range(1, 5):
      topo.add_host("w" + str(i))

    for i in range(1, 5):
      topo.add_host("fw" + str(i))

    self.host_map = { "h1" : { "ip" : "167772417", "mac" : "8796093022481" },
                      "h2" : { "ip" : "167772674", "mac" : "8796093022754" },
                      "h3" : { "ip" : "167772931", "mac" : "8796093023027" },
                      "h4" : { "ip" : "167773188", "mac" : "8796093023300" },
                      "w1" : { "ip" : "167773445", "mac" : "8796093023573" },
                      "w2" : { "ip" : "167773702", "mac" : "8796093023846" },
                      "w3" : { "ip" : "167773959", "mac" : "8796093024119" },
                      "w4" : { "ip" : "167774216", "mac" : "8796093024392" },
                      "fw1" : { "ip" : "167774473", "mac" : "8796093024665" },
                      "fw2" : { "ip" : "167774730", "mac" : "8796093026320" },
                      "fw3" : { "ip" : "167774987", "mac" : "8796093026577" },
                      "fw4" : { "ip" : "167775244", "mac" : "8796093026834" }
                    }

    self.public_web_server_ip = "3232235521"; #192.168.0.1

    # host access links
    topo.add_link("h1", "s1", 0, 1, 1)
    topo.add_link("h2", "s1", 0, 2, 1)
    topo.add_link("h3", "s1", 0, 3, 1)
    topo.add_link("h4", "s1", 0, 4, 1)

    topo.add_link("fw1", "s2", 0, 2, 1)
    topo.add_link("fw2", "s2", 0, 3, 1)
    topo.add_link("fw3", "s2", 0, 4, 1)
    topo.add_link("fw4", "s2", 0, 5, 1)

    topo.add_link("w1", "s3", 0, 2, 1)
    topo.add_link("w2", "s3", 0, 3, 1)
    topo.add_link("w3", "s3", 0, 4, 1)
    topo.add_link("w4", "s3", 0, 5, 1)

    # switch-switch links
    topo.add_link("s1", "s2", 6, 1, 1)
    topo.add_link("s1", "s3", 5, 6, 1)
    topo.add_link("s2", "s3", 6, 1, 1)

    self.topo = topo

  
  def init_counters(self):
    self.cntrs = {}
    self.port_cnt = {}
    for switch in self.topo.switches():
        self.cntrs[switch] = {}
        ports = len(list(self.topo.neighbors(switch)))
        self.port_cnt[switch] = ports 
        for i in range(ports):
            self.cntrs[switch][i] = 0
         
  def __init__(self, port=9000):
    super().__init__(port)
    self.init_topo()
    self.init_counters()
    self.up_switch_cnt = 0
    
    self.server_cnt = 1
    self.server_bill = 0
    self.prev_server_bill_update = time.time()
    
    self.fw_cnt = 1
    self.fw_bill = 0
    self.prev_fw_bill_update = time.time()

    # clear stats files
    for i in range(4):
        f = open(f"stats/h{i + 1}.txt", "w")
        f.close()

    f = open("stats/bills.txt", "w")
    f.close()

    # scaling variables
    self.ups = 0
    self.downs = 0
    self.last_avg_latency = 0
    self.last_fail_fraction = 0

  def get_latency_stats(self, cnt): 
    stats = []
    for i in range(4):
        f = open(f"stats/h{i + 1}.txt", "r")
        lines = f.readlines()
        f.close()

        lines.reverse()
        valid_cnt = 0
        for line in lines:
          parts = [x.strip() for x in line.split()]
          if len(parts) != 3:
              continue
          
          (time_stamp, latency, success) = [float(x) for x in parts]
          stats.append((time_stamp, latency, success))
          valid_cnt += 1
          if (valid_cnt == cnt):
              break
          
    stats.sort(reverse = True)
    stats = stats[:cnt]

    ok = 0.0
    not_ok = 0.0
    time_sum = 0.0
    for (_, latency, success) in stats:
        if success:
            ok += 1
            time_sum += latency
        else:
            not_ok += 1

    average_time = time_sum/ok if ok > 0 else 0
    fail_fraction = not_ok/(ok + not_ok) if (ok + not_ok) > 0 else 0
    return (average_time, fail_fraction)
    
  def change_server_cnt(self, cnt):
    assert(isinstance(cnt, int))
   
    print(f"Changing server cnt to {cnt}") 
    entry = Entry("active_server_cnt", [("meta.ph_key", "1")], "set_active_server_cnt", [("cnt", str(cnt))])
    self.insert("s3", entry)

    change_time = time.time()
    elapsed = change_time - self.prev_server_bill_update
    self.server_bill += elapsed * self.server_cnt 
    
    self.server_cnt = cnt
    self.prev_server_bill_update = change_time

  def change_fw_cnt(self, cnt):
    assert(isinstance(cnt, int))

    print(f"Changing firewall cnt to {cnt}") 
    entry = Entry("active_fw_cnt", [("meta.ph_key", "1")], "set_active_fw_cnt", [("cnt", str(cnt))])
    self.insert("s2", entry)

    change_time = time.time()
    elapsed = change_time - self.prev_fw_bill_update
    self.fw_bill += elapsed * self.fw_cnt

    self.fw_cnt = cnt
    self.prev_fw_bill_update = change_time

  def update_bills(self):
    # servers
    change_time = time.time()
    elapsed = change_time - self.prev_server_bill_update
    self.server_bill += elapsed * self.server_cnt 
    self.prev_server_bill_update = change_time

    # firewalls
    change_time = time.time()
    elapsed = change_time - self.prev_fw_bill_update
    self.fw_bill += elapsed * self.fw_cnt
    self.prev_fw_bill_update = change_time

  def print_counters(self):
    for switch in self.cntrs:
        print(f"{switch} countrs:")
        for port in self.cntrs[switch]:
            print(f"{port + 1}: {self.cntrs[switch][port]}")
        print("---------------")

  def get_server_cnt(self):
    return self.server_cnt

  def get_fw_cnt(self):
    return self.fw_cnt

  def elastic_scaling(self):
    def f():
      (avg_latency, fail_fraction) = self.get_latency_stats(20)
      print(f"latency stats: {avg_latency}, {fail_fraction}, {avg_latency * 1.1}, {self.last_avg_latency * 1.1}")

      if self.last_avg_latency == 0:
          self.last_avg_latency = avg_latency
          self.fail_fraction = fail_fraction

      else:
          if (avg_latency > self.last_avg_latency * (1.1) or
              fail_fraction > self.last_fail_fraction):
              self.downs = 0
              self.ups += 1
              print(f"performance is getting WORSE for the past {self.ups} times")
              if (self.ups >= 3):
                  self.ups = 0
                  cur_server_cnt = self.get_server_cnt()
                  if (cur_server_cnt < 4):
                    self.change_server_cnt(cur_server_cnt + 1)
                    if (self.get_server_cnt() > 2):
                        cur_fw_cnt = self.get_fw_cnt()
                        if (cur_fw_cnt < 4):
                            self.change_fw_cnt(cur_fw_cnt + 1)    

          elif (avg_latency * 1.1 < self.last_avg_latency and
                   fail_fraction == 0):
              self.ups = 0
              self.downs += 1

              print(f"performance is getting BETTER for the past {self.downs} times")
              
              if (self.downs >= 3):
                  self.downs = 0
                  cur_server_cnt = self.get_server_cnt()
                  if (cur_server_cnt > 1):
                    self.change_server_cnt(cur_server_cnt - 1)
                    if (self.get_server_cnt() <= 2):
                        cur_fw_cnt = self.get_fw_cnt()
                        if (cur_fw_cnt > 1):
                            self.change_fw_cnt(cur_fw_cnt - 1)    

          else:
              self.ups = 0
              self.downs = 0
              
          self.last_avg_latency = avg_latency
          self.last_fail_fraction = fail_fraction
 
      IOLoop.instance().call_later(delay = 5, callback = f)
      
    f()
 
  def poll_counters(self):
    def f():
        self.print_counters()
        for switch in self.cntrs:
            for port in self.cntrs[switch]:
                self.counter_request(switch, "port_cntr", port)
        IOLoop.instance().call_later(delay=5, callback=f)

    f()
      
  def counter_response(self, switch, name, index, count):
    self.cntrs[switch][index] = count
  
  def switch_up(self,switch,ports):
    print(f"{switch} is up!")
    
    if switch == "s1":
        for i in range(1, 5):
            host_id = "h" + str(i)
            dst_ip = self.host_map[host_id]["ip"]
            dst_mac = self.host_map[host_id]["mac"]
            entry = Entry("ipv4", [("hdr.ipv4.dstAddr", dst_ip)], "ipv4_forward", [("dstAddr", dst_mac), ("port", str(i))])
            self.insert(switch, entry)
            
    if switch == "s2":
        cnt = str(self.fw_cnt)
        entry = Entry("active_fw_cnt", [("meta.ph_key", "1")], "set_active_fw_cnt", [("cnt", cnt)])
        self.insert(switch, entry)
 
    if switch == "s3":
        cnt = str(self.server_cnt)
        entry = Entry("active_server_cnt", [("meta.ph_key", "1")], "set_active_server_cnt", [("cnt", cnt)])
        self.insert(switch, entry)

        for i in range(0, 4):
            ind = i + 1
            server_id = "w" + str(ind);
            server_ip = self.host_map[server_id]["ip"]
            server_mac = self.host_map[server_id]["mac"]
            port = str(ind + 1)
            entry = Entry("set_dst", [("meta.server_id", str(i))], "fw", [("ip_addr", server_ip), ("mac_addr", server_mac), ("port", port)])
            self.insert(switch, entry)

            entry = Entry("set_src", [("hdr.ipv4.srcAddr", server_ip)], "set_vip", [("addr", self.public_web_server_ip)])
            self.insert(switch, entry)

    self.up_switch_cnt += 1
    if (self.up_switch_cnt == 3):
        self.poll_counters()
        self.elastic_scaling()
 
    return

app = MyApp()
def sigint_handler(sig, frame):
    app.update_bills()
    f = open("stats/bills.txt", "w")
    f.write(f"{app.server_bill} {app.fw_bill}")
    f.close()
    sys.exit(0)

signal.signal(signal.SIGINT, sigint_handler)
app.start()


