from petr4 import App
from topo import *
from petr4.runtime import *
from tornado.ioloop import *

SWITCHES_EXPECTED = 7
CTRL_PT = 510
CTRL_MAC = "00:00:00:00:00:00" #TODO
CTRL_MAC = CTRL_MAC.replace(":", "")
DISCOVERY_ETHERTYPE = "2A2A"

def switch_mac(switch):
    return CTRL_MAC #TODO

class DiscoveryApp(App):            
    
    def discover_topo(self):
        
        if len(self.switches) != SWITCHES_EXPECTED:
            IOLoop.instance().call_later(delay=3, callback=self.discover_topo)
            # TODO: Does this get stack overflow eventually? seems not to...

        else:
            
            for i in range(1, 5):
                self.topo.add_host("h" + str(i))
                # TODO: handle host links?

            for key, value in self.switches.items():
                self.topo.add_switch(key)
                ethernet_hdr = CTRL_MAC + switch_mac(key) + DISCOVERY_ETHERTYPE
                switch_id = "0" + key.replace("s", "")
                discovery_hdr = switch_id + "FFFF"
                self.packet_out(key, CTRL_PT, ethernet_hdr + discovery_hdr)
    
    def __init__(self, port=9000):
        super().__init__(port)
        self.switches = dict()
        self.topo = Topology()
        self.discover_topo()

    def switch_up(self, switch, ports):
        self.switches[switch] = ports
        print(f"there are currently {len(self.switches)} switches available")
        super().switch_up(switch, ports)

app = DiscoveryApp()
app.start()
