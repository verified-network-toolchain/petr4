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
            print("There is already a link in the topology between %s and %s with weight %d." \
                    % (n1, n2, self.G.edges[n1][n2]["weight"]))
            return
        ports = { n1 : n1_port, n2 : n2_port } 
        self.G.add_edge(n1, n2, ports = ports, weight = weight)

    def switches(self):
        return [n for n, attr in self.G.nodes(data = True) if attr["typ"] == "switch"]

    def hosts(self):
        return [n for n, attr in self.G.nodes(data = True) if attr["typ"] == "host"]

    def links(self):
        return self.G.edges

    def port(self,n1,n2):
        if self.G.has_edge(n1,n2):
            return self.G.edges[n1,n2]["ports"][n1]
        else:
            print(f"There is no edge between {n1} and {n2}")
            return

    def modify_link_weight(self, n1, n2, weight):
        if not n1 in self.G.edges or not n2 in self.G.edges[n1]:
            print("Link (%s, %s) does not exist in the topology." % (n1, n2))
            return

        self.G.edges[n1][n2]["weight"] = weight

    def e2e_shortest_path(self):
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

    def next_hop(self, sw_id, dst_host_id):
        if not sw_id in self.G.nodes or \
           self.G.nodes[sw_id]["typ"] != "switch" or \
           not dst_host_id in self.G.nodes or \
           self.G.nodes[dst_host_id]["typ"] != "host":
            
            print("invalid switch id or host id")
            return None

        (_, path) = nx.single_source_dijkstra(self.G, sw_id)
        
        if not dst_host_id in path:
            print ("%s is not reachable from %s." % (dst_host_id, sw_id))
            return None

        return path[dst_host_id][1]
