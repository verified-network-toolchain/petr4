from petr4 import App
from topo import *
from petr4.runtime import *
from tornado.ioloop import *
from struct import pack
import binascii

class LearningApp(App):
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

        self.topo = topo

    def switch_up(self,switch,ports):
        spanning_tree_map = {
            "s1" : [],
            "s2" : [ 4 ],
            "s3" : [ 2, 3 ],
            "s4" : [],
            "s5" : [ 2 ],
            "s6" : [ 1 ],
            "s7" : [ 2 ] }
        print(f"{switch} is up!")
        for p in spanning_tree_map[switch]:
            entry = Entry("spanning_tree_filter", [("standard_metadata.egress_port", p)], "drop", [])
            self.insert(switch, entry)
        return
                
    def packet_in(self,switch,in_port,packet):
        # TODO
        super().packet_in(switch, in_port, packet)
        
    def __init__(self, port=9000):
        super().__init__(port)
        self.init_topo()

app = LearningApp()
app.start()
