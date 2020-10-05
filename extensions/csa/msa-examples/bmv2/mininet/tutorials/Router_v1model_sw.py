#!/usr/bin/env python2

#
# Author: Hardik Soni
# Email: hks57@cornell.edu
#

import sys
import os
from mininet.net import Mininet
from mininet.topo import Topo
from mininet.node import Node
from mininet.log import setLogLevel, info
from mininet.cli import CLI

sys.path.insert(1, './bmv2/mininet/')
sys.path.insert(1, './../')

# Get the value of
P4_MININET_PATH = os.environ['P4_MININET_PATH']
if P4_MININET_PATH is None:
    print("P4_MININET_PATH is not set, p4_mininet may not be found")
# Print the value of
print("P4_MININET_PATH", P4_MININET_PATH)
sys.path.insert(1, P4_MININET_PATH)
from p4_mininet import P4Switch, P4Host


import argparse
from time import sleep

parser = argparse.ArgumentParser(description='Mininet demo')
parser.add_argument('--behavioral-exe', help='Path to behavioral executable',
                    type=str, action="store", required=True)
parser.add_argument('--thrift-port', help='Thrift server port for table updates',
                    type=int, action="store", default=9090)
parser.add_argument('--num-hosts', help='Number of hosts to connect to switch',
                    type=int, action="store", default=2)
parser.add_argument('--json', help='Path to JSON config file',
                    type=str, action="store", required=True)
parser.add_argument('--pcap-dump', help='Dump packets on interfaces to pcap files',
                    type=str, action="store", required=False, default=False)

args = parser.parse_args()

class IPv6Node( Node ):
    def config( self, ipv6, ipv6_gw=None, **params ):
        super( IPv6Node, self).config( **params )
        self.cmd( 'ip -6 addr add %s dev %s' % ( ipv6, self.defaultIntf() ) )
        #if ipv6_gw:
        #  self.cmd( 'ip -6 route add default via %s' % ( ipv6_gw ) )
        # Enable SRv6
        #self.cmd( 'sysctl -w net.ipv6.conf.all.seg6_enabled=1' )
        #self.cmd( 'sysctl -w net.ipv6.conf.%s.seg6_enabled=1' % self.defaultIntf() )
        # Enable forwarding on the router:
        #self.cmd( 'sysctl -w net.ipv6.conf.all.forwarding=1' )

    def terminate( self ):
        #self.cmd( 'sysctl -w net.ipv6.conf.all.forwarding=0' )
        super( IPv6Node, self ).terminate()



class SingleSwitchTopo(Topo):
    "Single switch connected to n (< 256) hosts."
    def __init__(self, sw_path, json_path, thrift_port, pcap_dump, n, **opts):
        # Initialize topology and default options
        Topo.__init__(self, **opts)

        switch = self.addSwitch('s1',
                                sw_path = sw_path,
                                json_path = json_path,
                                thrift_port = thrift_port,
                                pcap_dump = pcap_dump,
                                log_console = True,
                                enable_debugger = True)

        for h in xrange(n):
            host = self.addHost('h%d' % (h + 1),
                    cls = IPv6Node,  ipv6='202'+str(h + 1)+'::1/64', 
                                ip = "10.0.%d.1/24" % (h+1),
                                mac = '00:00:00:00:00:%02x' %(h+1))
            self.addLink(host, switch)



def main():
    num_hosts = args.num_hosts

    topo = SingleSwitchTopo(args.behavioral_exe,
                            args.json,
                            args.thrift_port,
                            args.pcap_dump,
                            num_hosts)
    net = Mininet(topo = topo,
                  host = P4Host,
                  switch = P4Switch,
                  controller = None)


    net.start()
    sw_mac = ["00:aa:bb:00:00:%02x" % (n+1) for n in xrange(num_hosts)]
    sw_addr = ["10.0.%d.1" % (n+1) for n in xrange(num_hosts)]
    gw_addr = ["10.0.%d.254" % (n+1) for n in xrange(num_hosts)]
    sw_addr6 = ["202%d::1" % (n+1) for n in xrange(num_hosts)]
    gw_addr6 = ["202%d::10" % (n+1) for n in xrange(num_hosts)]

    for n in xrange(num_hosts):
        h = net.get('h%d' % (n + 1))
        h.cmd('arp -s ' +gw_addr[n] +' '+ sw_mac[n])
        h.cmd(' route add default gw ' +gw_addr[n] +' '+ str(h.defaultIntf()))
        h.cmd('ethtool -K '+str(h.defaultIntf())+' rx off ')
        h.cmd('ethtool -K '+str(h.defaultIntf())+' tx off ')
        h.cmd('ip -6 neigh add '+ gw_addr6[n] +' lladdr '+ sw_mac[n]+ ' dev '+ str(h.defaultIntf()))
        h.cmd('ip -6 route add default via '+ gw_addr6[n])
        for k in xrange(num_hosts):
            if n == k:
                continue
            # h.cmd('ip -6 neigh add '+ sw_addr6[k] +' lladdr '+ sw_mac[k]+ ' dev '+ str(h.defaultIntf()))
            # print 'ip -6 neigh add '+ sw_addr6[k] +' lladdr '+ sw_mac[k]+ ' dev '+ str(h.defaultIntf())
        # print 'dev '+str(h.defaultIntf())+' via ' + sw_addr[n]
        # h.setDefaultRoute("dev "+str(h.defaultIntf())+" via %s" % sw_addr[n])

    sleep(3)

    print "Ready !"

    # enable following line and type h1 ping h2 on the CLI
    print "Ipv6 ping command"
    print "h1 ping -6 2001::2"
    CLI( net ) 
    # net.pingAll()
    # for n in xrange(num_hosts):
    #    h = net.get('h%d' % (n + 1))
    #    for k in xrange(num_hosts):
    #        if n == k:
    #            continue
    #        out, err, ec = h.pexec('ping -6  '+ sw_addr6[k]+' -c 3')
    #        print(str(h)+ ' ping -6  '+ sw_addr6[k]+' -c ')
    #        print(out)

    net.stop()

if __name__ == '__main__':
    setLogLevel( 'info' )
    main()
