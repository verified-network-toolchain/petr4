# An trivial application that does nothing
from petr4 import App
from topo import *
from optimizer import *
from petr4.runtime import *
from tornado.ioloop import *
import sys

class MyApp(App):
  def init_topo(self):
    topo = Topology()
  
    sw_cnt = 12;
    
    for i in range(1, sw_cnt + 1):
      topo.add_switch("s" + str(i))

    for i in range(1, 5):
      topo.add_host("h" + str(i))

    self.host_map = { "h1" : { "ip" : "167772417", "mac" : "8796093022481" },
                      "h2" : { "ip" : "167772674", "mac" : "8796093022754" },
                      "h3" : { "ip" : "167772931", "mac" : "8796093023027" },
                      "h4" : { "ip" : "167773188", "mac" : "8796093023300" } }

    # host access links
    topo.add_link("h1", "s1", 0, 1, 1)
    topo.add_link("h2", "s2", 0, 1, 1)
    topo.add_link("h3", "s11", 0, 4, 1)
    topo.add_link("h4", "s12", 0, 4, 1)

    # switch-switch links
    topo.add_link("s1", "s3", 3, 1, 1)
    topo.add_link("s1", "s4", 2, 1, 1)

    topo.add_link("s2", "s4", 3, 2, 1)
    topo.add_link("s2", "s5", 2, 1, 1)

    topo.add_link("s3", "s4", 2, 6, 1)
    topo.add_link("s3", "s6", 3, 1, 1)

    topo.add_link("s4", "s5", 3, 3, 1)
    topo.add_link("s4", "s6", 5, 2, 1)
    topo.add_link("s4", "s7", 4, 1, 1)

    topo.add_link("s5", "s7", 2, 2, 1)

    topo.add_link("s6", "s8", 5, 1, 1)
    topo.add_link("s6", "s9", 3, 1, 1)
    topo.add_link("s6", "s11", 4, 2, 1)

    topo.add_link("s7", "s9", 5, 2, 1)
    topo.add_link("s7", "s10", 3, 1, 1)
    topo.add_link("s7", "s12", 4, 2, 1)
    
    topo.add_link("s8", "s9", 2, 6, 1)
    topo.add_link("s8", "s11", 3, 1, 1)
 
    topo.add_link("s9", "s10", 3, 3, 1)
    topo.add_link("s9", "s11", 5, 3, 1)
    topo.add_link("s9", "s12", 4, 1, 1)

    topo.add_link("s10", "s12", 2, 3, 1) 
    self.topo = topo 

  def init_demands(self):
    demands = {}
    
    demands["h1", "h3"] = 5 
    demands["h2", "h3"] = 3
    demands["h4", "h3"] = 1 
    demands["h1", "h4"] = 1 
    demands["h2", "h4"] = 5 
    
    self.demands = demands

    demand_ids = {}

    demand_ids["h1", "h3"] = 0 
    demand_ids["h2", "h3"] = 2
    demand_ids["h4", "h3"] = 4 
    demand_ids["h1", "h4"] = 6 
    demand_ids["h2", "h4"] = 8

    self.demand_ids = demand_ids; 


  def optimize_paths(self): 
    solver = Optimizer(ObjectiveType.MIN)
    vs = {}

    for d in self.demands:
      src, dst = d
      for a, b in self.topo.links():
        if ((a in self.topo.hosts() and a != src and a != dst) or
           (b in self.topo.hosts() and b != src and b != dst)):
          continue
        solver.add_integer_var(f"{d}_on_({a}, {b})",
                               lower_bound = 0,
                               upper_bound = self.demands[d])
        solver.add_integer_var(f"{d}_on_({b}, {a})",
                               lower_bound = 0,
                               upper_bound = self.demands[d])

    # flow conservation on each switch
    for d in self.demands:
      for s in self.topo.switches():
        nei = self.topo.neighbors(s)
        incoming = []
        outgoing = []
        for n in nei:
            incoming_var_name = f"{d}_on_({n}, {s})"
            if (incoming_var_name in solver.vars):
              incoming.append(solver.vars[incoming_var_name])

            outgoing_var_name = f"{d}_on_({s}, {n})"
            if (outgoing_var_name in solver.vars):
              outgoing.append(solver.vars[outgoing_var_name])

        solver.add_constraint(f"conserve_{d}_on_{s}", 
                              incoming, "==", outgoing)
    
    # flow conservation at the src
    for d in self.demands:
      src = d[0]
      nei = self.topo.neighbors(src)
      incoming = []
      outgoing = []
      for n in nei:
        incoming_var_name = f"{d}_on_({n}, {src})"
        incoming.append(solver.vars[incoming_var_name])

        outgoing_var_name = f"{d}_on_({src}, {n})"
        outgoing.append(solver.vars[outgoing_var_name])

      solver.add_constraint(f"conserve_{d}_at_{src}", 
                            outgoing, "==", incoming + [self.demands[d]])

    # flow conservation at the dst
    for d in self.demands:
      dst = d[1]
      nei = self.topo.neighbors(dst)
      incoming = []
      outgoing = []
      for n in nei:
        incoming_var_name = f"{d}_on_({n}, {dst})"
        incoming.append(solver.vars[incoming_var_name])

        outgoing_var_name = f"{d}_on_({dst}, {n})"
        outgoing.append(solver.vars[outgoing_var_name])

      solver.add_constraint(f"conserve_{d}_at_{dst}",
                            incoming, "==", outgoing + [self.demands[d]])

    solver.add_integer_var(f"max_util", lower_bound = 0)
    
    for a, b in self.topo.links():
      if (not a in self.topo.switches() or 
          not b in self.topo.switches()):
        continue

      rhs_1 = []
      rhs_2 = []
      for d in self.demands:
        var_name = f"{d}_on_({a}, {b})"
        rhs_1.append(solver.vars[var_name])

        var_name = f"{d}_on_({b}, {a})"
        rhs_2.append(solver.vars[var_name])

      solver.add_constraint(f"util_for_({a}, {b})",
                            rhs_1, "<=", [solver.vars["max_util"]])

      solver.add_constraint(f"util_for_({b}, {a})",
                            rhs_2, "<=", [solver.vars["max_util"]])
    
    solver.add_objective_function(solver.vars["max_util"]) 
    
    self.path_assignments = solver.solve()
    for v in self.path_assignments:
      print(f"{v}: {self.path_assignments[v]}")

    self.paths = {}
    for d in self.demands:
      print(d)
      src, dst = d
      cur_path = [src]
      rem_paths = []
      all_paths = []
      n = src
      done = False
      while not done:
        nei = self.topo.neighbors(n)
        non_zero = []
        for x in nei:
          var_name = f"{d}_on_({n}, {x})"
          if var_name in self.path_assignments:
            val = self.path_assignments[var_name]
            if val > 0:
              non_zero.append(x)
        next_node = non_zero[0]
        if next_node == dst:
          cur_path += [dst]
          all_paths.append(cur_path)
          print(cur_path)
          if len(rem_paths) > 0:
            cur_path = rem_paths[0]
            rem_paths = rem_paths[1:]
            n = cur_path[-1]
          else:
            done = True
        else:
          for x in non_zero[1:]:
            rem_paths.append(cur_path + [x])
          cur_path.append(next_node)
          n = next_node

      self.paths[d] = all_paths
      
      print("\n")    

    
  def track_counters(self):
    self.port_cnt = {}
    for sw in self.topo.switches():
      nei = list(self.topo.neighbors(sw))
      self.port_cnt[sw] = len(nei)
     
    self.cntrs = {}
    for sw in self.topo.switches():
      self.cntrs[sw] = {}
      for j in range(1, self.port_cnt[sw] + 1):
        self.cntrs[sw][j] = 0

    
    self.reports = {}
    for sw in self.topo.switches():
      self.reports[sw] = 0

    self.check_reports()
     
  def __init__(self, port=9000):
    super().__init__(port)
    self.init_topo()
    self.init_demands()
    self.optimize_paths()
    self.track_counters()


  def check_reports(self):
    def f():
        done = True
        for sw in self.reports:
            if self.reports[sw] < self.port_cnt[sw]:
                done = False
                break
        if done:
            cnts = []
            for sw in self.cntrs:
                print(f"{sw} counters:")
                for port in self.cntrs[sw]:
                    cnt = self.cntrs[sw][port]
                    nei_node = self.topo.neighbor_on_port(sw, port)
                    if nei_node in self.topo.switches():
                      cnts.append(cnt)
                      print(f"port {port}: {cnt}")
            max_cnt = max(cnts)
            print(f"Max Count: {max_cnt}")
            sys.exit(0)

        IOLoop.instance().call_later(delay=5, callback = f)
    f()

  def poll_counter(self, switch):
    def f():
      for i in range(self.port_cnt[switch]):
        self.counter_request(switch, "port_cntr", i)
    
    IOLoop.instance().call_later(delay=30, callback=f)

  def counter_response(self, switch, name, index, count):
    self.cntrs[switch][index + 1] = count
    self.reports[switch] += 1
 
  def switch_up(self,switch,ports):
                     
    print(f"{switch} is up!")
   
    for d in self.demands:
      src, dst = d

      nei = self.topo.neighbors(switch)
      incoming = []
      outgoing = [] 
      for n in nei:
        var_name = f"{d}_on_({n}, {switch})"
        if var_name in self.path_assignments:
          val = int(self.path_assignments[var_name])
          if val > 0:
            incoming.append((n, val))

        var_name = f"{d}_on_({switch}, {n})"
        if var_name in self.path_assignments:
          val = int(self.path_assignments[var_name])
          if val > 0:
            outgoing.append((n, val))

      if len(outgoing) > 0:
        src_ip = self.host_map[src]["ip"]

        dst_ip = self.host_map[dst]["ip"]
        dst_mac = self.host_map[dst]["mac"]
      
        demand_id = str(self.demand_ids[d])
        valid_ports = str(len(outgoing))
        
        port_params = []
        for i, p in enumerate(outgoing):
          port_name = "port%d" % (i + 1)
          port_val = str(self.topo.port(switch, p[0]))
          port_params.append((port_name, port_val))

          weight_name = "weight%d" % (i + 1)
          weight_val = str(p[1])
          port_params.append((weight_name, weight_val))

        for i in range(len(outgoing), 5):
          port_name = "port%d" % (i + 1)
          port_params.append((port_name, "20"))

          weight_name = "weight%d" % (i + 1)
          port_params.append((weight_name, "0"))
 
       
        entry = Entry("ipv4", [("hdr.ipv4.srcAddr", src_ip), ("hdr.ipv4.dstAddr", dst_ip)], "ipv4_forward", 
                              [("demand_id", demand_id), ("dstAddr", dst_mac), ("valid_ports", valid_ports)] + port_params)

        self.insert(switch, entry)

      '''
      if len(incoming) > 0:
        src_ip = self.host_map[dst]["ip"]

        dst_ip = self.host_map[src]["ip"]
        dst_mac = self.host_map[src]["mac"]
      
        demand_id = str(self.demand_ids[d] + 1)
        valid_ports = str(len(incoming))
        
        port_params = []
        for i, p in enumerate(incoming):
          port_name = "port%d" % (i + 1)
          port_val = str(self.topo.port(switch, p[0]))
          port_params.append((port_name, port_val))

          weight_name = "weight%d" % (i + 1)
          weight_val = str(p[1])
          port_params.append((weight_name, weight_val))

        for i in range(len(incoming), 5):
          port_name = "port%d" % (i + 1)
          port_params.append((port_name, "20"))

          weight_name = "weight%d" % (i + 1)
          port_params.append((weight_name, "0"))
 
       
        entry = Entry("ipv4", [("hdr.ipv4.srcAddr", src_ip), ("hdr.ipv4.dstAddr", dst_ip)], "ipv4_forward", 
                              [("demand_id", demand_id), ("dstAddr", dst_mac), ("valid_ports", valid_ports)] + port_params)

        self.insert(switch, entry)
    '''
    self.poll_counter(switch)
    return

app = MyApp()
app.start()

