import networkx as nx

class Topology:

    def __init__(self):
        self.G = nx.Graph()
   
    def add_switch(self, sw_id):
        if sw_id in self.G.nodes:
            print ("%s is already in the topology as a %s." \
                    % (sw_id, self.G.nodes[sw_id]["typ"]))
            return

        self.G.add_node(sw_id, typ = "switch")


    def add_host(self, h_id):
        if h_id in self.G.nodes:
            print ("%s is already in the topology as a %s." \
                    % (h_id, self.G.nodes[h_id]["typ"]))
            return

        self.G.add_node(h_id, typ = "host")


    def add_link(self, n1, n2, n1_port, n2_port, weight):
        if self.G.has_edge(n1,n2):
            return
        ports = { n1 : n1_port, n2 : n2_port } 
        self.G.add_edge(n1, n2, ports = ports, weight = weight)

    def switches(self):
        return [n for n, attr in self.G.nodes(data = True) if attr["typ"] == "switch"]

    def hosts(self):
        return [n for n, attr in self.G.nodes(data = True) if attr["typ"] == "host"]

    def links(self):
        return self.G.edges

    def neighbors(self, n):
        return self.G.neighbors(n)
    
    def port(self,n1,n2):
        if self.G.has_edge(n1,n2):
            return self.G.edges[n1,n2]["ports"][n1]
        else:
            print(f"There is no edge between {n1} and {n2}")
            return
   
    def neighbor_on_port(self, n, p):
        nei = self.neighbors(n)
        for x in nei:
            if self.port(n, x) == p:
                return x
        return None

    def modify_link_weight(self, n1, n2, weight):
        if not (n1, n2) in self.G.edges:
            print("Link (%s, %s) does not exist in the topology." % (n1, n2))
            return

        self.G.edges[n1, n2]["weight"] = weight

    def shortest_path(self, src_id, dst_id):
        if not src_id in self.G.nodes or \
           not dst_id in self.G.nodes:
            
            print("invalid src id or dst id")
            return None

        (_, path) = nx.single_source_dijkstra(self.G, src_id, target = dst_id)
        return path

    def e2e_shortest_paths(self):
        res = {}
        paths = dict(nx.all_pairs_dijkstra_path(self.G))
        for n1 in paths:
            if self.G.nodes[n1]["typ"] == "switch":
                continue

            for n2 in paths[n1]:
                if self.G.nodes[n2]["typ"] == "switch" or \
                   n1 == n2:
                    continue

                res[n1, n2] = paths[n1][n2][1: -1]

        return res

    def shortest_path_next_hop(self, sw_id, dst_host_id):
        if not sw_id in self.G.nodes or \
           self.G.nodes[sw_id]["typ"] != "switch" or \
           not dst_host_id in self.G.nodes or \
           self.G.nodes[dst_host_id]["typ"] != "host":
            
            print("invalid switch id or host id")
            return None

        path = self.shortest_path(sw_id, dst_host_id)
        if path is None:
            print ("%s is not reachable from %s." % (dst_host_id, sw_id))
            return None
        else:
            return path[1]

    def weight(self, path):
        res = 0
        if len(path) < 2:
            return None

        for i, n1 in enumerate(path[:-1]):
            n2 = path[i + 1]
            if not n1 in self.G.nodes or \
               not n2 in self.G.nodes:
                   print ("Invalid node on input path.")
                   return None
            
            res += self.G.edges[n1, n2]["weight"]

        return res

    def all_simple_paths(self, src_id, dst_id):
        try:
            paths = nx.shortest_simple_paths(self.G, src_id, dst_id, weight = "weight")
            paths_with_weights = []
            for path in paths:
                paths_with_weights.append((path, self.weight(path)))
        except nx.NetworkXError:
            print("invalid src id or dst id")
            return None
        except nx.NetworkXNoPath:
            print("%s is not reachable from %s." % (dst_id, src_id))
            return None
        
        return paths_with_weights
