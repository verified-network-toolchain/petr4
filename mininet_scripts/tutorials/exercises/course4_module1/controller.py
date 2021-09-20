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

    topo.add_host("h1")
    topo.add_host("h2")
    topo.add_host("fw")
    topo.add_host("lb")
    topo.add_host("w1")
    topo.add_host("w2")
    topo.add_host("w3")
    topo.add_host("w4")

    self.host_map = { "h1" : { "ip" : "167772417", "mac" : "8796093022481" },
                      "h2" : { "ip" : "167772674", "mac" : "8796093022754" },
                      "lb" : { "ip" : "167772931", "mac" : "8796093023027" },
                      "fw" : { "ip" : "167773188", "mac" : "8796093023300" },
                      "w1" : { "ip" : "167773445", "mac" : "8796093023573" },
                      "w2" : { "ip" : "167773702", "mac" : "8796093023846" },
                      "w3" : { "ip" : "167773959", "mac" : "8796093024119" },
                      "w4" : { "ip" : "167774216", "mac" : "8796093024392" } 
                    }

    # host access links
    topo.add_link("h1", "s1", 0, 1, 1)
    topo.add_link("h2", "s1", 0, 2, 1)
    topo.add_link("fw", "s1", 0, 3, 1)
    topo.add_link("lb", "s1", 0, 4, 1)

    topo.add_link("w1", "s2", 0, 1, 1)
    topo.add_link("w2", "s2", 0, 2, 1)
    topo.add_link("w3", "s2", 0, 3, 1)
    topo.add_link("w4", "s2", 0, 4, 1)

    # switch-switch links
    topo.add_link("s1", "s3", 5, 1, 1)
    topo.add_link("s2", "s3", 5, 2, 1)

    self.topo = topo
    paths = topo.e2e_shortest_paths()
    self.paths = {}
    for n1, n2 in paths:
      self.paths[n1, n2] = [n1] + paths[n1, n2] + [n2]

    print ("e2e paths:")
    for n1, n2 in self.paths:
        if n1 < n2:
            print("%s %s: %s" % (n1, n2, str(self.paths[n1, n2]))) 
    print("")
  
         
  def __init__(self, port=9000):
    super().__init__(port)
    self.init_topo()

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
    
    return

app = MyApp()
app.start()

