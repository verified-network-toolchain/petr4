# An trivial application that does nothing
from petr4 import App
from topo import *
from petr4.runtime import *
from tornado.ioloop import *
import sys

class MyApp(App):
  def init_topo(self):
    topo = Topology()
    
    for i in range(1, 4):
      topo.add_switch("s" + str(i))

    for i in range(1, 5):
      topo.add_host("h" + str(i))

    for i in range(1, 5):
      topo.add_host("w" + str(i))

    self.host_map = { "h1" : { "ip" : "167772417", "mac" : "8796093022481" },
                      "h2" : { "ip" : "167772674", "mac" : "8796093022754" },
                      "h3" : { "ip" : "167772931", "mac" : "8796093023027" },
                      "h4" : { "ip" : "167773188", "mac" : "8796093023300" },
                      "w1" : { "ip" : "167773445", "mac" : "8796093023573" },
                      "w2" : { "ip" : "167773702", "mac" : "8796093023846" },
                      "w3" : { "ip" : "167773959", "mac" : "8796093024119" },
                      "w4" : { "ip" : "167774216", "mac" : "8796093024392" } 
                    }

    self.public_web_server_ip = "167774730";

    # host access links
    topo.add_link("h1", "s1", 0, 1, 1)
    topo.add_link("h2", "s1", 0, 2, 1)
    topo.add_link("h3", "s1", 0, 3, 1)
    topo.add_link("h4", "s1", 0, 4, 1)

    topo.add_link("w1", "s2", 0, 1, 1)
    topo.add_link("w2", "s2", 0, 2, 1)
    topo.add_link("w3", "s2", 0, 3, 1)
    topo.add_link("w4", "s2", 0, 4, 1)

    # switch-switch links
    topo.add_link("s1", "s3", 5, 1, 1)
    topo.add_link("s2", "s3", 5, 2, 1)

    self.topo = topo
  
         
  def __init__(self, port=9000):
    super().__init__(port)
    self.init_topo()

  def switch_up(self,switch,ports):
    print(f"{switch} is up!")
    
    if switch == "s1":
        for i in range(0, 3):
            ind = i + 1
            dst_ip = self.host_map["w" + str(ind)]["ip"]
            
            entry = Entry("set_dst", [("meta.server_id", str(i))], "set_dip", [("addr", dst_ip)])
            self.insert(switch, entry)
                    
        for i in range(1, 4):
            src_ip = self.host_map["w" + str(i)]["ip"]
            
            entry = Entry("set_src", [("hdr.ipv4.srcAddr", src_ip)], "set_vip", [("addr", self.public_web_server_ip)])
            self.insert(switch, entry)

    for h in self.topo.hosts():
        p = self.topo.shortest_path(switch, h)
        next_hop = p[1]
        port = str(self.topo.port(switch, next_hop))
        
        dst_ip = self.host_map[h]["ip"]
        dst_mac = self.host_map[h]["mac"]
  
        entry = Entry("ipv4", [("hdr.ipv4.dstAddr", dst_ip)], "ipv4_forward", [("dstAddr", dst_mac), ("port", port)])
        self.insert(switch, entry)

    
    return

app = MyApp()
app.start()

