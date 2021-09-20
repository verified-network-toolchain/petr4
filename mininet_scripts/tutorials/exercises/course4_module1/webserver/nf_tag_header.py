from scapy.all import *
import sys, os

PROTO_NF_TAG = 145
PROTO_TCP = 6 

class NFTag(Packet):
    name = "nf_tag"
    fields_desc = [
        ByteField("tag", 0),
        ByteField("protocol", 0)
    ]
    def mysummary(self):
        return self.sprintf("tag=%tag%, protocol=%protocol%")


bind_layers(IP, NFTag, proto=PROTO_NF_TAG)
bind_layers(NFTag, TCP, protocol=PROTO_TCP)
