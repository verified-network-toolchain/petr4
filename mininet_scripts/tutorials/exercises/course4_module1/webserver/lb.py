from scapy.all import *
from nf_tag_header import NFTag
import random

public_addr = "10.0.10.10"
servers = ["10.0.5.5", "10.0.6.6", "10.0.7.7", "10.0.8.8"]
mapping = {}

def get_if():
    ifs=get_if_list()
    iface=None
    for i in get_if_list():
        if "eth0" in i:
            iface=i
            break;
    if not iface:
        print("Cannot find eth0 interface")
        exit(1)
    return iface

def handle_pkt(pkt):
    if (IP in pkt and 
      pkt[IP].dst == public_addr and
      NFTag in pkt and
      TCP in pkt):

      key = (pkt[IP].src, pkt[TCP].sport)
      if not key in mapping:
          #ind = random.randint(0, len(servers) - 1)
          ind = 0
          mapping[key] = servers[ind]
      
      del pkt[IP].chksum        
      pkt[IP].dst = mapping[key] 
      pkt[NFTag].tag = 5
      pkt.show2()
      sys.stdout.flush()
      hexdump(pkt)
      sendp(pkt, iface = get_if())

def incoming(pkt):
    return (IP in pkt and NFTag in pkt and pkt[NFTag].tag == 4)

def main():
    iface = get_if()
    print(("sniffing on %s" % iface))
    sys.stdout.flush()
    sniff(iface = iface,
          prn = lambda x: handle_pkt(x),
          lfilter=incoming)

if __name__ == '__main__':
    main()
