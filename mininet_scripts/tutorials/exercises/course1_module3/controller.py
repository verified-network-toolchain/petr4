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
        topo.add_link("h1", "s1", 1, 1, 1)
        topo.add_link("h2", "s2", 1, 1, 1)
        topo.add_link("h3", "s3", 1, 1, 1)

        # switch-switch links
        topo.add_link("s1", "s2", 2, 2, 1)
        topo.add_link("s1", "s3", 3, 2, 1)
        topo.add_link("s2", "s3", 3, 3, 1)

        self.topo = topo

    def switch_up(self,switch,ports):
        spanning_tree_map = {
            "s1" : [ 1,2,3 ],
            "s2" : [ 1,2 ],
            "s3" : [ 1,2 ] }
        print(f"{switch} is up!")
        for p in spanning_tree_map[switch]:
            entry = Entry("spanning_tree", [("standard_metadata.egress_port", str(p))], "pass", [])
            
            self.insert(switch, entry)
        return
                
    def packet_in(self,switch,in_port,packet):
        port = packet[:33]
        dst = packet[33:]
        entry = Entry("ethernet_learning", [("hdr.ipv4.dstAddr", dst), "forward", [port])
        self.insert(switch, entry)
        
    def __init__(self, port=9000):
        super().__init__(port)
        self.init_topo()

app = LearningApp()
app.start()
