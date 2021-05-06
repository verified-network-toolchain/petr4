import networkx as nx

class Topology:

    def __init__(self):
        self.G = nx.Graph()
   
    def add_switch(self, sw_id):
        if sw_id in self.G.node:
            print ("%s is already in the topology as a %s." \
                    % (sw_id, self.G.node[sw_id]["typ"]))
            return

        self.G.add_node(sw_id, typ = "switch")


    def add_host(self, h_id):
        if h_id in self.G.node:
            print ("%s is already in the topology as a %s." \
                    % (h_id, self.G.node[h_id]["typ"]))
            return

        self.G.add_node(h_id, typ = "host")


    def add_link(self, n1, n2, weight):
        if n1 in self.G.edge and n2 in self.G.edge[n1]:
            print("There is already a link in the topology between %s and %s with weight %d." \
                    % (n1, n2, self.G.edge[n1][n2]["weight"]))
            return

        self.G.add_edge(n1, n2, weight = weight)


    def switches(self):
        return [n for n, attr in self.G.nodes(data = True) if attr["typ"] == "switch"]

    def hosts(self):
        return [n for n, attr in self.G.nodes(data = True) if attr["typ"] == "host"]

    def links(self):
        return self.G.edge

    def modify_link_weight(self, n1, n2, weight):
        if not n1 in self.G.edge or not n2 in self.G.edge[n1]:
            print("Link (%s, %s) does not exist in the topology." % (n1, n2))
            return

        self.G.edge[n1][n2]["weight"] = weight

    def e2e_shortest_path(self):
        res = {}
        paths = dict(nx.all_pairs_dijkstra_path(self.G))
        for n1 in paths:
            if self.G.node[n1]["typ"] == "switch":
                continue

            for n2 in paths[n1]:
                if self.G.node[n2]["typ"] == "switch" or \
                   n1 == n2:
                    continue

                res[n1, n2] = paths[n1][n2][1: -1]


        return res

    def next_hop(self, sw_id, dst_host_id):
        if not sw_id in self.G.node or \
           self.G.node[sw_id]["typ"] != "switch" or \
           not dst_host_id in self.G.node or \
           self.G.node[dst_host_id]["typ"] != "host":
            
            print "invalid switch id or host id"
            return None

        (_, path) = nx.single_source_dijkstra(self.G, sw_id)
        
        if not dst_host_id in path:
            print ("%s is not reachable from %s." % (dst_host_id, sw_id))
            return None

        return path[dst_host_id][1]

if __name__ == "__main__":
    topo = Topology()

    for i in range(1, 8):
        topo.add_switch("s" + str(i))

    for i in range(1, 5):
        topo.add_host("h" + str(i))

    # host access links
    topo.add_link("h1", "s1", 1)
    topo.add_link("h2", "s2", 1)
    topo.add_link("h3", "s6", 1)
    topo.add_link("h4", "s7", 1)

    # switch-switch links
    topo.add_link("s1", "s3", 1)
    topo.add_link("s1", "s4", 2)

    topo.add_link("s2", "s3", 1)
    topo.add_link("s2", "s4", 1)
    topo.add_link("s2", "s5", 1)

    topo.add_link("s3", "s6", 3)

    topo.add_link("s4", "s6", 1)
    topo.add_link("s4", "s7", 7)

    topo.add_link("s5", "s7", 1)

    # compute shortest paths
    paths = topo.e2e_shortest_path()

    print ("e2e shortest paths:")
    for n1, n2 in paths:
        if n1 < n2:
            print("%s %s: %s" % (n1, n2, str(paths[n1, n2]))) 
    print("")


    for n1 in topo.switches():
        print("%s routing table: " % n1)
        for n2 in topo.hosts():
            print ("%s --> %s" % (n2, topo.next_hop(n1, n2)))

        print ("")
