#!/usr/bin/env python
import sys
import struct
import os
import time
import signal

from scapy.all import sniff, sendp, hexdump, get_if_list, get_if_hwaddr, get_if_addr
from scapy.all import Packet, IPOption
from scapy.all import ShortField, IntField, LongField, BitField, FieldListField, FieldLenField
from scapy.all import IP, TCP, UDP, Raw
from scapy.layers.inet import _IPOption_HDR

rcvd_flows = {}

def get_time():
    return time.time() * 1000
def get_if():
    ifs=get_if_list()
    iface=None
    for i in get_if_list():
        if "eth0" in i:
            iface=i
            break;
    if not iface:
        exit(1)
    return iface

def handle_pkt(pkt):
    now = get_time()
    if TCP in pkt and pkt[TCP].dport == 1234:
        srcip = pkt[IP].src
        if not srcip in rcvd_flows:
            rcvd_flows[srcip] = [now, 0, 1]
        rcvd_flows[srcip][1] = now
        rcvd_flows[srcip][2] += 1 

def main():
    ifaces = filter(lambda i: 'eth' in i, os.listdir('/sys/class/net/'))
    iface = ifaces[0]

    sniff(iface = iface,
          prn = lambda x: handle_pkt(x),
          timeout = 30)
    
    host_ip = get_if_addr(get_if()) 
    stats_file = open("tg_scripts/stats/receiver_%s.txt" % str(host_ip), 'w')
    for f in rcvd_flows:
        f_stats = [str(x) for x in rcvd_flows[f]]
        stats_file.write("%s %s\n" % (f, ' '.join(f_stats)))

    stats_file.close()
    sys.exit(0)


if __name__ == '__main__':
    main()
