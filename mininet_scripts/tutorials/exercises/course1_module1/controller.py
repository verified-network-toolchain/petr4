# An trivial application that does nothing
from petr4 import App
from topo import *
from petr4.runtime import *

class MyApp(App):
  def init_topo(self):
    topo = Topology()
    
    for i in range(1, 8):
      topo.add_switch("s" + str(i))

    for i in range(1, 5):
      topo.add_host("h" + str(i))

    # host access links
    topo.add_link("h1", "s1", 0, 1, 1)
    topo.add_link("h2", "s2", 0, 1, 1)
    topo.add_link("h3", "s6", 0, 3, 1)
    topo.add_link("h4", "s7", 0, 3, 1)

    # switch-switch links
    topo.add_link("s1", "s3", 3, 1, 1)
    topo.add_link("s1", "s4", 2, 1, 1)

    topo.add_link("s2", "s3", 4, 2, 1)
    topo.add_link("s2", "s4", 3, 2, 1)
    topo.add_link("s2", "s5", 2, 1, 1)

    topo.add_link("s3", "s6", 3, 1, 1)

    topo.add_link("s4", "s6", 4, 2, 1)
    topo.add_link("s4", "s7", 3, 1, 1)

    topo.add_link("s5", "s7", 2, 2, 1)
    
    ### TODO: fill in costs here ###
    ### ...
    
    # compute shortest paths
    paths = topo.e2e_shortest_path()

    self.topo = topo
    self.paths = paths

    print ("e2e shortest paths:")
    for n1, n2 in paths:
        if n1 < n2:
            print("%s %s: %s" % (n1, n2, str(paths[n1, n2]))) 
    print("")

#    for n1 in topo.switches():
#        print("%s routing table: " % n1)
#        for n2 in topo.hosts():
#            print ("%s --> %s" % (n2, topo.next_hop(n1, n2)))
#        print ("")
        
  def __init__(self, port=9000):
    super().__init__(port)
    self.init_topo()
    
  def switch_up(self,switch,ports):
    host_map = { "h1" : { "ip" : "167772417", "mac" : "8796093022481" },
                 "h2" : { "ip" : "167772674", "mac" : "8796093022754" },
                 "h3" : { "ip" : "167772931", "mac" : "8796093023027" },
                 "h4" : { "ip" : "167773188", "mac" : "8796093023300" } }
                 
    print(f"{switch} is up!")
    for host in self.topo.hosts():
      next_hop = self.topo.next_hop(switch,host)
      port = str(self.topo.port(switch,next_hop))
      ip = host_map[host]["ip"]
      mac = host_map[host]["mac"]
      entry = Entry("ipv4", [("hdr.ipv4.dstAddr", ip)], "ipv4_forward", [("dstAddr", mac), ("port", port)])
      self.insert(switch, entry)
    return

app = MyApp()
app.start()

