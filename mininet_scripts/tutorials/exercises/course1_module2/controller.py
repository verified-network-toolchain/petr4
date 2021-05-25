from petr4 import App
from topo import *
from petr4.runtime import *
from tornado.ioloop import *
from struct import pack
import binascii

SWITCHES_EXPECTED = 7
CTRL_PT = 510
CTRL_MAC = "00:00:00:00:00:00" #TODO
DISCOVERY_ETHERTYPE = "2A2A"

def switch_mac(switch):
    return "ffffffffffff"

class DiscoveryApp(App):            
    
    def discover_topo(self):
        for key, value in self.switches.items():
            packet = "000000000000" + switch_mac(key) + "2a2a" + "0" + key[1] + "ff" + "ff" + "00"
            self.packet_out(key, CTRL_PT, packet)
        IOLoop.instance().call_later(delay=5, callback=self.discover_topo)

    def switch_up(self,switch,ports):
        hosts = { "s1" : ("h1", 0, 1, 1),
                  "s2" : ("h2", 0, 1, 1),
                  "s6" : ("h3", 0, 3, 1),
                  "s7" : ("h4", 0, 3, 1) }
        self.topo.add_switch(switch)
        if switch in hosts:
            (h, pt1, pt2, w) = hosts[switch]
            self.topo.add_host(h)
            self.topo.add_link(h, switch, pt1, pt2, w)
        self.switches[switch] = ports
        print(f"there are currently {len(self.switches)} switches available")
        super().switch_up(switch, ports)
                
    def packet_in(self,switch,in_port,packet):
        start_switch = "s" + packet[29:30]
        start_pt = packet[30:32]
        end_pt = packet[32:34]
        print(f"{start_switch} : {start_pt } -> {switch} : {end_pt}")
        self.topo.add_link(start_switch, switch, int(start_pt), int(end_pt), 1)

        print ("e2e shortest paths:")
        paths = self.topo.e2e_shortest_paths()
        for n1, n2 in paths:
            if n1 < n2:
                print("%s %s: %s" % (n1, n2, str(paths[n1, n2]))) 
        print("")
        
    def __init__(self, port=9000):
        super().__init__(port)
        self.switches = dict()
        self.topo = Topology()
        self.discover_topo()

app = DiscoveryApp()
app.start()
