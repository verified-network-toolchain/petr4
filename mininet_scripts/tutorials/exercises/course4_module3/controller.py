# An trivial application that does nothing
from petr4 import App
from topo import *
from petr4.runtime import *
from tornado.ioloop import *
import sys

class MyApp(App):
  def init_topo(self):
    topo = Topology()
    
    for i in range(1, 4):
      topo.add_switch("s" + str(i))

    for i in range(1, 5):
      topo.add_host("h" + str(i))

    for i in range(1, 5):
      topo.add_host("w" + str(i))

    self.host_map = { "h1" : { "ip" : "167772417", "mac" : "8796093022481" },
                      "h2" : { "ip" : "167772674", "mac" : "8796093022754" },
                      "h3" : { "ip" : "167772931", "mac" : "8796093023027" },
                      "h4" : { "ip" : "167773188", "mac" : "8796093023300" },
                      "w1" : { "ip" : "167773445", "mac" : "8796093023573" },
                      "w2" : { "ip" : "167773702", "mac" : "8796093023846" },
                      "w3" : { "ip" : "167773959", "mac" : "8796093024119" },
                      "w4" : { "ip" : "167774216", "mac" : "8796093024392" },
                      "fw1" : { "ip" : "167774473", "mac" : "8796093024665" },
                      "fw2" : { "ip" : "167774730", "mac" : "8796093026320" },
                      "fw3" : { "ip" : "167774987", "mac" : "8796093026577" },
                      "fw4" : { "ip" : "167775244", "mac" : "8796093026834" }
                    }

    self.public_web_server_ip = "3232235521"; #192.168.0.1

    # host access links
    topo.add_link("h1", "s1", 0, 1, 1)
    topo.add_link("h2", "s1", 0, 2, 1)
    topo.add_link("h3", "s1", 0, 3, 1)
    topo.add_link("h4", "s1", 0, 4, 1)

    topo.add_link("fw1", "s2", 0, 2, 1)
    topo.add_link("fw2", "s2", 0, 3, 1)
    topo.add_link("fw3", "s2", 0, 4, 1)
    topo.add_link("fw4", "s2", 0, 5, 1)

    topo.add_link("w1", "s3", 0, 2, 1)
    topo.add_link("w2", "s3", 0, 3, 1)
    topo.add_link("w3", "s3", 0, 4, 1)
    topo.add_link("w4", "s3", 0, 5, 1)

    # switch-switch links
    topo.add_link("s1", "s2", 6, 1, 1)
    topo.add_link("s1", "s3", 5, 6, 1)
    topo.add_link("s2", "s3", 6, 1, 1)

    self.topo = topo
  
         
  def __init__(self, port=9000):
    super().__init__(port)
    self.init_topo()

  def switch_up(self,switch,ports):
    print(f"{switch} is up!")
    
    if switch == "s1":
        for i in range(1, 5):
            host_id = "h" + str(i)
            dst_ip = self.host_map[host_id]["ip"]
            dst_mac = self.host_map[host_id]["mac"]
            entry = Entry("ipv4", [("hdr.ipv4.dstAddr", dst_ip)], "ipv4_forward", [("dstAddr", dst_mac), ("port", str(i))])
            self.insert(switch, entry)
            
    if switch == "s2":
        cnt = "4"
        entry = Entry("active_fw_cnt", [("meta.ph_key", "1")], "set_active_fw_cnt", [("cnt", cnt)])
        self.insert(switch, entry)
 
    if switch == "s3":
        cnt = "4"
        entry = Entry("active_server_cnt", [("meta.ph_key", "1")], "set_active_server_cnt", [("cnt", cnt)])
        self.insert(switch, entry)

        for i in range(0, 4):
            ind = i + 1
            server_id = "w" + str(ind);
            server_ip = self.host_map[server_id]["ip"]
            server_mac = self.host_map[server_id]["mac"]
            port = str(ind + 1)
            entry = Entry("set_dst", [("meta.server_id", str(i))], "fw", [("ip_addr", server_ip), ("mac_addr", server_mac), ("port", port)])
            self.insert(switch, entry)

            entry = Entry("set_src", [("hdr.ipv4.srcAddr", server_ip)], "set_vip", [("addr", self.public_web_server_ip)])
            self.insert(switch, entry)
 
    return

app = MyApp()
app.start()

