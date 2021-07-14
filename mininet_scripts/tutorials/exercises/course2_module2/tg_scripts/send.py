#!/usr/bin/env python
import argparse
import sys
import socket
import random
import struct
import time

from scapy.all import sendp, send, get_if_list, get_if_hwaddr, get_if_addr
from scapy.all import Packet
from scapy.all import Ether, IP, UDP, TCP

def get_time():
    return time.time() * 1000
def get_if():
    ifs=get_if_list()
    iface=None # "h1-eth0"
    for i in get_if_list():
        if "eth0" in i:
            iface=i
            break;
    if not iface:
        print "Cannot find eth0 interface"
        exit(1)
    return iface

def main():

    if len(sys.argv)<3:
        print 'pass 2 arguments: <destination> "<num_pkts>"'
        exit(1)

    addr = socket.gethostbyname(sys.argv[1])
    num_pkts = int(sys.argv[2])
    msg = 'a' * 1000 
 
    iface = get_if()

    start = get_time() 
    for i in range(num_pkts):
        pkt =  Ether(src=get_if_hwaddr(iface), dst='ff:ff:ff:ff:ff:ff')
        pkt = pkt /IP(dst=addr) / TCP(dport=1234, sport=random.randint(49152,65535)) / msg
        #pkt.show2()
        sendp(pkt, iface=iface, verbose=False)
    end = get_time()

    src_addr = get_if_addr(iface)

    stat_file = open("tg_scripts/stats/sender_%s_%s.txt" % (str(src_addr), str(addr)), 'w')
    stat_file.write("%s %s\n" % (str(start), str(end)))
    stat_file.close()

if __name__ == '__main__':
    main()
