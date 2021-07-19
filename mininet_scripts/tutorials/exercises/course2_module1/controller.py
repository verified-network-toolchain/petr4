# An trivial application that does nothing
from petr4 import App
from topo import *
from petr4.runtime import *
from tornado.ioloop import *
import sys

class MyApp(App):
  def init_topo(self):
    topo = Topology()
    
    for i in range(1, 8):
      topo.add_switch("s" + str(i))

    for i in range(1, 5):
      topo.add_host("h" + str(i))

    self.host_map = { "h1" : { "ip" : "167772417", "mac" : "8796093022481" },
                      "h2" : { "ip" : "167772674", "mac" : "8796093022754" },
                      "h3" : { "ip" : "167772931", "mac" : "8796093023027" },
                      "h4" : { "ip" : "167773188", "mac" : "8796093023300" } }

    # host access links
    topo.add_link("h1", "s1", 0, 1, 1)
    topo.add_link("h2", "s2", 0, 1, 1)
    topo.add_link("h3", "s6", 0, 3, 1)
    topo.add_link("h4", "s7", 0, 3, 1)

    # switch-switch links
    topo.add_link("s1", "s2", 4, 3, 1)
    topo.add_link("s1", "s3", 3, 1, 1)
    topo.add_link("s1", "s4", 2, 1, 1)

    topo.add_link("s2", "s4", 2, 2, 1)

    topo.add_link("s3", "s4", 2, 6, 1)
    topo.add_link("s3", "s6", 3, 2, 1)

    topo.add_link("s4", "s5", 3, 1, 1)
    topo.add_link("s4", "s6", 5, 1, 1)
    topo.add_link("s4", "s7", 4, 2, 1)

    topo.add_link("s5", "s7", 2, 1, 1)
    
    paths = {}
    paths["h1", "h3"] = ["h1", "s1", "s3", "s6", "h3"]

    paths["h2", "h3"] = ["h2", "s2", "s4", "s6", "h3"]

    #paths["h4", "h3"] = ["h4", "s7", "s4", "s3", "s6", "h3"]
    paths["h4", "h3"] = ["h4", "s7", "s4", "s6", "h3"]

    paths["h1", "h4"] = ["h1", "s1", "s4", "s7", "h4"]

    #paths["h2", "h4"] = ["h2", "s2", "s1", "s3", "s4", "s5", "s7", "h4"]
    paths["h2", "h4"] = ["h2", "s2", "s4", "s7", "h4"]

    self.topo = topo
    self.paths = paths

    print ("e2e shortest paths:")
    for n1, n2 in paths:
        if n1 < n2:
            print("%s %s: %s" % (n1, n2, str(paths[n1, n2]))) 
    print("")
  
  def poll_counter(self, switch):
    def f():
      for i in range(self.port_cnt[switch]):
        self.counter_request(switch, "port_cntr", i)
    
    IOLoop.instance().call_later(delay=30, callback=f)

  def counter_response(self, switch, name, index, count):
    self.cntrs[switch][index + 1] = count
    self.reports[switch] += 1
       
  def __init__(self, port=9000):
    super().__init__(port)
    self.init_topo()

    self.port_cnt = {}
    for i in [1, 3, 6, 7]:
        sw = f"s{i}"
        self.port_cnt[sw] = 3

    for i in [2, 5]:
        sw = f"s{i}"
        self.port_cnt[sw] = 2

    self.port_cnt["s4"] = 6

     
    self.cntrs = {}
    for i in range(1, 8):
        sw = f"s{i}"
        self.cntrs[sw] = {}
        for j in range(1, self.port_cnt[sw] + 1):
            self.cntrs[sw][j] = 0

    
    self.reports = {}
    for i in range(1, 8):
        sw = f"s{i}"
        self.reports[sw] = 0

    self.check_reports()

  def check_reports(self):
    def f():
        done = True
        for sw in self.reports:
            if self.reports[sw] < self.port_cnt[sw]:
                done = False
                break
        if done:
            cnts = []
            for sw in self.cntrs:
                print(f"{sw} counters:")
                for port in self.cntrs[sw]:
                    cnt = self.cntrs[sw][port]
                    nei_node = self.topo.neighbor_on_port(sw, port)
                    if nei_node in self.topo.switches():
                      cnts.append(cnt)
                      print(f"port {port}: {cnt}")
            max_cnt = max(cnts)
            print(f"Max Count: {max_cnt}")
            sys.exit(0)

        IOLoop.instance().call_later(delay=5, callback = f)
    f()

  def switch_up(self,switch,ports):
                     
    print(f"{switch} is up!")
    for src, dst in self.paths:
        p = self.paths[src, dst]
        if switch in p:
            ind = p.index(switch)
            # we are sure there is a next hope
            # because the hosts are in the path too
            next_hop = p[ind + 1]
            port = str(self.topo.port(switch, next_hop))
            
            src_ip = self.host_map[src]["ip"]

            dst_ip = self.host_map[dst]["ip"]
            dst_mac = self.host_map[dst]["mac"]
      
            entry = Entry("ipv4", [("hdr.ipv4.srcAddr", src_ip), ("hdr.ipv4.dstAddr", dst_ip)], "ipv4_forward", [("dstAddr", dst_mac), ("port", port)])
            self.insert(switch, entry)
    
    self.poll_counter(switch)
    return

app = MyApp()
app.start()

