from topo import *

topo = Topology()

for i in range(1, 8):
  topo.add_switch("s" + str(i))

for i in range(1, 5):
  topo.add_host("h" + str(i))

# host access links
topo.add_link("h1", "s1", 0, 1, 1)
topo.add_link("h2", "s2", 0, 1, 1)
topo.add_link("h3", "s6", 0, 3, 1)
topo.add_link("h4", "s7", 0, 3, 1)

# switch-switch links
topo.add_link("s1", "s3", 3, 1, 1)
topo.add_link("s1", "s4", 2, 1, 2)

topo.add_link("s2", "s3", 4, 2, 1)
topo.add_link("s2", "s4", 3, 2, 1)
topo.add_link("s2", "s5", 2, 1, 1)

topo.add_link("s3", "s6", 3, 1, 3)

topo.add_link("s4", "s6", 4, 2, 1)
topo.add_link("s4", "s7", 3, 1, 3)

topo.add_link("s5", "s7", 2, 2, 1)

paths = {}

for n1 in topo.hosts():
    for n2 in topo.hosts():
        if n1 >= n2:
            continue
        
        if n1 == "h1" and n2 == "h3":
            paths[n1, n2] = topo.shortest_path(n1, n2)
        
        else:
            subpaths1 = topo.all_simple_paths(n1, "s2")
            subpaths2 = topo.all_simple_paths("s2", n2)


            # Make sure we pick a combination that is not a loop
            # This may not be necessary in our graph, as the shortest
            # path from an end host to s2 does not have any nodes in common
            # with the shortest path from s2 to another end host.
            
            valid_combs = []
            for p1, c1 in subpaths1:
                for p2, c2 in subpaths2:
                    p2 = p2[1:]
                    intersection = set(p1) & set(p2)
                    if len(intersection) == 0:
                        valid_combs.append((c1 + c2, p1 + p2))
            valid_combs.sort()
            paths[n1, n2] = valid_combs[0][1]

for n1, n2 in paths:
    if n1 < n2:
        print("%s %s: %s" % (n1, n2, str(paths[n1, n2][1:-1]))) 
print("")

for n in topo.switches():
    print("%s routing table: " % n)
    for h1, h2 in paths:
        p = paths[h1, h2]
        if n in p:
            ind = p.index(n)
            print ("(%s, %s) --> %s" % (h1, h2, p[ind + 1]))
            print ("(%s, %s) --> %s" % (h2, h1, p[ind - 1]))
    print ("")

