from petr4 import App
from topo import *
from petr4.runtime import *

SWITCHES_EXPECTED = 7

class DiscoveryApp(App):
    def discover_topo(self):
        print("discover topology entry point reached")
        
        topo = Topology()

        for i in range(1, 5):
            topo.add_host("h" + str(i))

        # while len(self.switches) < 7:
          #  print("still in while loop")
           # yield gen.sleep(0.5)

        print("All of the switches are up!")

        
    
    def __init__(self, port=9000):
        super().__init__(port)
        self.switches = dict()
        self.discover_topo()

    def switch_up(self, switch, ports):
        self.switches[switch] = ports
        print(f"there are currently {len(self.switches)} switches available")
        super().switch_up(switch, ports)

app = DiscoveryApp()
app.start()
