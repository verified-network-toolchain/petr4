#!/usr/bin/env python
import sys
import struct

from scapy.all import sniff, get_if_list, bind_layers
from scapy.all import Packet, ByteField, XShortField, IntField
from scapy.all import Ether, IP

def get_if():
    ifs=get_if_list()
    iface=None
    for i in get_if_list():
        if "eth0" in i:
            iface=i
            break;
    if not iface:
        print "Cannot find eth0 interface"
        exit(1)
    return iface

class Telemetry(Packet):
    fields_desc = [ IntField("maxFlows", 0),
                    IntField("maxDelay", 0),
                    XShortField("etherType", 0)]

bind_layers(Telemetry, IP, etherType=0x0800)
bind_layers(Ether, Telemetry, type=0x9999)

def handle_pkt(pkt):
    print "Received a packet"
    pkt.show2()
    sys.stdout.flush()

def main():
    iface = 'eth0'
    print "Sniffing on %s" % iface
    sys.stdout.flush()
    sniff(iface = iface,
          prn = lambda x: handle_pkt(x))

if __name__ == '__main__':
    main()
