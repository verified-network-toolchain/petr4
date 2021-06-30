from petr4 import App
from topo import *
from petr4.runtime import *
from tornado.ioloop import *
from struct import pack
import binascii
from collections import defaultdict

def mk_broadcast(packet):
    return packet[0:24] + "8888" + packet[24:]

def mk_mac_key(mac):
    return str(int(mac,16))

class LearningApp(App):

    mac_table = defaultdict(lambda:{})
    
    def switch_up(self,switch,ports):
        print(f"Switch_Up { switch }")
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
        dst_mac = packet[0:12]
        src_mac = packet[12:24]
        self.mac_table[switch][src_mac] = in_port
        if(dst_mac in self.mac_table[switch].keys()):
            out_port = self.mac_table[switch][dst_mac]
            keys = [("hdr.ethernet.dstAddr", mk_mac_key(dst_mac)), ("hdr.ethernet.srcAddr", mk_mac_key(src_mac))]
            action = "forward"
            action_data = [("port", str(out_port))]
            entry = Entry("ethernet_learning", keys, action, action_data)
            self.insert(switch, entry)
            self.packet_out(switch, in_port, packet)
        else:
            self.packet_out(switch, in_port, mk_broadcast(packet))
        
    def __init__(self, port=9000):
        super().__init__(port)

app = LearningApp()
app.start()
