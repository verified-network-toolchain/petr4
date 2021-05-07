# Copyright 2013-present Barefoot Networks, Inc.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

from mininet.net import Mininet
from mininet.node import Switch, Host
from mininet.log import setLogLevel, info, error, debug
from mininet.moduledeps import pathCheck
from sys import exit
import os
import tempfile

class P4Host(Host):
    def config(self, **params):
        r = super(Host, self).config(**params)

        self.defaultIntf().rename("eth0")

        for off in ["rx", "tx", "sg"]:
            cmd = "/sbin/ethtool --offload eth0 %s off" % off
            self.cmd(cmd)

        # disable IPv6
        self.cmd("sysctl -w net.ipv6.conf.all.disable_ipv6=1")
        self.cmd("sysctl -w net.ipv6.conf.default.disable_ipv6=1")
        self.cmd("sysctl -w net.ipv6.conf.lo.disable_ipv6=1")

        return r

    def describe(self):
        print "**********"
        print self.name
        print "default interface: %s\t%s\t%s" %(
            self.defaultIntf().name,
            self.defaultIntf().IP(),
            self.defaultIntf().MAC()
        )
        print "**********"


class Petr4Switch(Switch):
    """Petr4 switch"""
    device_id = 0

    def __init__(self, name, 
                 sw_path = None, 
                 p4_prog_path = None,
                 include_path = None,
                 **kwargs):
        Switch.__init__(self, name, **kwargs)
        assert(sw_path)
        assert(p4_prog_path)
        # make sure that the provided sw_path is valid
        pathCheck(sw_path)
        # make sure that the provided P4 program file exists
        if not os.path.isfile(p4_prog_path):
            error("Invalid P4 file.\n")
            exit(1)
        self.sw_path = sw_path
        self.p4_prog_path = p4_prog_path
        self.include_path = include_path
        self.log_file = "/tmp/p4s.{}.log".format(self.name)
        self.device_id = Petr4Switch.device_id
        Petr4Switch.device_id += 1
        self.nanomsg = "ipc:///tmp/bm-{}-log.ipc".format(self.device_id)

    @classmethod
    def setup(cls):
        pass

    def check_switch_started(self, pid):
        return os.path.exists(os.path.join("/proc", str(pid)))

    def start(self, controllers):
        "Start up a new Petr4 switch"
        info("Starting Petr4 switch {}.\n".format(self.name))
        args = [self.sw_path + " switch "]

        args.extend(['-switch', self.name])
        
        for port, intf in self.intfs.items():
            if not intf.IP():
                args.extend(['-i', str(port) + "@" + intf.name])
                                
        args.extend(['-I', self.include_path]) 
        
        Petr4Switch.device_id += 1
        
        args.append(self.p4_prog_path)
        
        info(' '.join(args) + "\n")

        pid = None
        with tempfile.NamedTemporaryFile() as f:
            cmd = ' '.join(args) + ' >' + self.log_file + ' 2>&1 & echo $! >> ' + f.name 
            print cmd + "\n"
            self.cmd(cmd)
            pid = int(f.read())
        debug("Petr4 switch {} PID is {}.\n".format(self.name, pid))
        if not self.check_switch_started(pid):
            error("Petr4 switch {} did not start correctly.\n".format(self.name))
            exit(1)
        info("Petr4 switch {} has been started.\n".format(self.name))

    def stop(self):
        "Terminate Petr4 switch."
        self.cmd('kill %' + self.sw_path)
        self.cmd('wait')
        self.deleteIntfs()

    def attach(self, intf):
        "Connect a data port"
        assert(0)

    def detach(self, intf):
        "Disconnect a data port"
        assert(0)
