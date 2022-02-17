#!/usr/bin/env python2
# Copyright 2013-present Barefoot Networks, Inc.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Adapted by Robert MacDavid (macdavid@cs.princeton.edu) from scripts found in
# the p4app repository (https://github.com/p4lang/p4app)
#
# We encourage you to dissect this script to better understand the BMv2/Mininet
# environment used by the P4 tutorial.
#
import os, sys, json, subprocess, re, argparse
from time import sleep

from p4_mininet import Petr4Switch, P4Host

from mininet.net import Mininet
from mininet.topo import Topo
from mininet.link import TCLink
from mininet.cli import CLI

def configureP4Switch(**switch_args):
    """ Helper class that is called by mininet to initialize
        the virtual P4 switches.
    """
    class ConfiguredPetr4Switch(Petr4Switch):
        def __init__(self, *opts, **kwargs):
            global next_port
            kwargs.update(switch_args)
            Petr4Switch.__init__(self, *opts, **kwargs)

        def describe(self):
            print "%s" % (self.name)

    return ConfiguredPetr4Switch 
    


class ExerciseTopo(Topo):
    """ The mininet topology class for the P4 tutorial exercises.
    """
    def __init__(self, hosts, switches, links, petr4_exe, p4_prog, include_path, **opts):
        Topo.__init__(self, **opts)
        host_links = []
        switch_links = []

        # assumes host always comes first for host<-->switch links
        for link in links:
            node1 = link['node1'].split('-')[0]
            node2 = link['node2'].split('-')[0]
            if node1 in switches and node2 in switches:
               switch_links.append(link)
            else:
                host_links.append(link)


        for sw, params in switches.iteritems():
            # TODO: do we need this? we should test it out
            if "program" in params:
                print sw, params["program"]
                switchClass = configureP4Switch(
                                sw_path= petr4_exe,
                                p4_prog_path= params["program"],
                                include_path = include_path)
            else:
                # add default switch
                switchClass = None
            self.addSwitch(sw, cls=switchClass)

        for link in host_links:
            node1 = link['node1'].split('-')[0]
            node2 = link['node2'].split('-')[0]

            host_node = "node1"
            sw_node = "node2"
            if node1 in switches:
              host_node = "node2"
              sw_node = "node1"   

            host_name = link[host_node]
            sw_name, sw_port = self.parse_switch_node(link[sw_node])
            host_ip = hosts[host_name]['ip']
            host_mac = hosts[host_name]['mac']
            self.addHost(host_name, ip=host_ip, mac=host_mac)
            self.addLink(host_name, sw_name,
                         delay=link['latency'], bw=link['bandwidth'],
                         port2=sw_port)

        for link in switch_links:
            sw1_name, sw1_port = self.parse_switch_node(link['node1'])
            sw2_name, sw2_port = self.parse_switch_node(link['node2'])
            self.addLink(sw1_name, sw2_name,
                        port1=sw1_port, port2=sw2_port,
                        delay=link['latency'], bw=link['bandwidth'])


    def parse_switch_node(self, node):
        assert(len(node.split('-')) == 2)
        sw_name, sw_port = node.split('-')
        try:
            sw_port = int(sw_port[1:])
        except:
            raise Exception('Invalid switch node in topology file: {}'.format(node))
        return sw_name, sw_port


class ExerciseRunner:
    """
        Attributes:
            hosts    : dict<string, dict> // mininet host names and their associated properties
            switches : dict<string, dict> // mininet switch names and their associated properties
            links    : list<dict>         // list of mininet link properties

            petr4_exe    : string // name or path of the p4 switch binary
            prog_file   : string // path to the p4 program
            include_path : string // path to core.p4 and architecture files

            topo : Topo object   // The mininet topology instance
            net : Mininet object // The mininet instance

    """
    def logger(self, *items):
        print(' '.join(items))

    def format_latency(self, l):
        """ Helper method for parsing link latencies from the topology json. """
        if isinstance(l, (str, unicode)):
            return l
        else:
            return str(l) + "ms"


    def __init__(self, topo_file,
                       petr4_exe='petr4',
                       p4_prog="", 
                       include_path=""):
        """ Initializes some attributes and reads the topology json. Does not
            actually run the exercise. Use run_exercise() for that.

            Arguments:
                topo_file : string    // A json file which describes the exercise's
                                         mininet topology.
                petr4_exe    : string  // Path to the p4 behavioral binary
        """

        self.logger('Reading topology file.')
        with open(topo_file, 'r') as f:
            topo = json.load(f)
        self.hosts = topo['hosts']
        self.switches = topo['switches']
        self.links = self.parse_links(topo['links'])

        self.p4_prog = p4_prog
        self.include_path = include_path
        self.petr4_exe = petr4_exe


    def run_exercise(self):
        """ Sets up the mininet instance, programs the switches,
            and starts the mininet CLI. This is the main method to run after
            initializing the object.
        """
        # Initialize mininet with the topology specified by the config
        self.create_network()
        self.net.start()
        sleep(1)

        # some programming that must happen after the net has started
        self.program_hosts()
        self.program_switches()

        # wait for that to finish. Not sure how to do this better
        sleep(1)

        self.do_experiment()
        #self.do_net_cli()
       
        # stop right after the CLI is exited
        self.net.stop()

    #TODO: lots of hard-coded stuff here
    def do_experiment(self):
        hosts = []
        for i in range(4):
            hosts.append(self.net.get("h%d" % (i + 1)))
      
        hosts[0].cmd("python3.9 webserver/client.py 192.168.0.1 8000 10 5 20 > stats/h1.txt &")
        sleep(10) 
        hosts[1].cmd("python3.9 webserver/client.py 192.168.0.1 8000 5 5 20 > stats/h2.txt &")

        sleep(20)
        hosts[2].cmd("python3.9 webserver/client.py 192.168.0.1 8000 10 5 10 > stats/h3.txt &")
        #hosts[3].cmd("python3.9 webserver/client.py 192.168.0.1 8000 10 1 10 > stats/h4.txt &")

        sleep(400)
        

    def parse_links(self, unparsed_links):
        """ Given a list of links descriptions of the form [node1, node2, latency, bandwidth]
            with the latency and bandwidth being optional, parses these descriptions
            into dictionaries and store them as self.links
        """
        links = []
        for link in unparsed_links:
            # make sure each link's endpoints are ordered alphabetically
            s, t, = link[0], link[1]
            if s > t:
                s,t = t,s

            link_dict = {'node1':s,
                        'node2':t,
                        'latency':'0ms',
                        'bandwidth':None
                        }
            if len(link) > 2:
                link_dict['latency'] = self.format_latency(link[2])
            if len(link) > 3:
                link_dict['bandwidth'] = link[3]

            if link_dict['node1'][0] == 'h':
                assert link_dict['node2'][0] == 's', 'Hosts should be connected to switches, not ' + str(link_dict['node2'])
            links.append(link_dict)
        return links


    def create_network(self):
        """ Create the mininet network object, and store it as self.net.

            Side effects:
                - Mininet topology instance stored as self.topo
                - Mininet instance stored as self.net
        """
        self.logger("Building mininet topology.")

        defaultSwitchClass = configureP4Switch(
                                sw_path=self.petr4_exe,
                                p4_prog_path=self.p4_prog,
                                include_path = self.include_path)

        self.topo = ExerciseTopo(self.hosts, self.switches, self.links, 
                                 self.petr4_exe, self.p4_prog, self.include_path)

        self.net = Mininet(topo = self.topo,
                      link = TCLink,
                      host = P4Host,
                      switch = defaultSwitchClass,
                      controller = None)

    
    def program_switches(self):
        """ TODO: This method will program each switch with rules/ etc.
            should complete this when we have the control interface
        """
        pass
        
        
    def program_hosts(self):
        """ Execute any commands provided in the topology.json file on each Mininet host
        """
        for host_name, host_info in self.hosts.items():
            h = self.net.get(host_name)
            if "commands" in host_info:
                for cmd in host_info["commands"]:
                    h.cmd(cmd)


    def do_net_cli(self):
        """ Starts up the mininet CLI and prints some helpful output.

            Assumes:
                - A mininet instance is stored as self.net and self.net.start() has
                  been called.
        """
        for s in self.net.switches:
            s.describe()
        for h in self.net.hosts:
            h.describe()
        self.logger("Starting mininet CLI")
        # Generate a message that will be printed by the Mininet CLI to make
        # interacting with the simple switch a little easier.
        print('')
        print('======================================================================')
        print('Welcome to the BMV2 Mininet CLI!')
        print('======================================================================')
        print('Your P4 program is installed into the BMV2 software switch')
        print('and your initial runtime configuration is loaded. You can interact')
        print('with the network using the mininet CLI below.')
        print('')

        CLI(self.net)


def get_args():
    cwd = os.getcwd()
    parser = argparse.ArgumentParser()
    parser.add_argument('-t', '--topo', help='Path to topology json',
                        type=str, required=False, default='./topology.json')
    parser.add_argument('-f', '--p4_prog', type=str, nargs="+", required=False)
    parser.add_argument('-I', '--include_path', type=str, required=False)
    parser.add_argument('-b', '--behavioral-exe', help='Path to petr4 executable',
                                type=str, required=False, default='petr4')
    return parser.parse_args()


if __name__ == '__main__':
    # from mininet.log import setLogLevel
    # setLogLevel("info")

    args = get_args()
    exercise = ExerciseRunner(args.topo,
                              args.behavioral_exe,
                              args.p4_prog, 
                              args.include_path)

    exercise.run_exercise()

