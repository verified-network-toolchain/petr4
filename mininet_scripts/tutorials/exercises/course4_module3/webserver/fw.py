from scapy.all import *

allowed_list = ["10.0.1.1", "10.0.2.2", "10.0.3.3", "10.0.4.4"]
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
    pkt.show2()
    if IP in pkt and pkt[IP].tos == 1: 
      if pkt[IP].src in allowed_list:
        pkt[IP].tos = 0
        sendp(pkt, iface = get_if())
        #pkt.show2()
        #sys.stdout.flush()

def incoming(pkt):
    return (IP in pkt and pkt[IP].tos == 1)

def main():
    iface = get_if()
    print(("sniffing on %s" % iface))
    sys.stdout.flush()
    sniff(iface = iface,
          prn = lambda x: handle_pkt(x),
          lfilter = incoming)

if __name__ == '__main__':
    main()
