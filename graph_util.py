import networkx as nx
from multiset import FrozenMultiset as Multiset

# Networkx's graph printing is abysmal / nonexistent.
# The pygraphviz library apparently prints graphs to console,
# yet I can't get it to install. So here's a shot
# at more visual graph printing.
def print_graph(G):
    for n in G.nodes_iter():
        print("\t{}".format(str(n)))
        for idx, e in enumerate(G.edges_iter(n, data='concept')):
            if idx == 0:
                print("\t |")
            print("\t %-26s%s" % ("'--" + e[2]['concept'] + "--->", e[1]))

# Calculate the probability of brute-forcing the given path.
# (i.e. by randomly choosing an out-edge at each node).
def bruteforce_prob_path(G, path):
    p = 1.0

    mid = path[:-1]
    for n in mid:
        # The probability of selecting the 'correct' edge
        # going out of this node. Assumes uniform dist.
        # In the future, dist. should be cond. on prior play history.
        p *= 1.0 / G.out_degree(n)

    return p

# Calculate the probability of brute-forcing
# from start_node and ending at end_node:
def bruteforce_prob(G, start_node, end_node):
    p = 0.0

    # There can be multiple simple paths leading to the end node.
    # The total probability is the sum of individual path probabilities.
    # > This uses nx.all_simple_paths's generator version for efficiency.
    for path in nx.all_simple_paths(G, source=start_node, target=end_node):
        p += bruteforce_prob_path(G, path)

    # Store for later
    # __bf_cache[(start_node, end_node)] = p

    return p

# Returns the node that's *least likely* to reach
# with a purely brute-force strategy.
# * This is calculated as the probability of choosing the
# right edge at each node along all paths.
# __bf_cache = dict()
def least_bruteforceable(G, start_node, nodes):

    # Calc. 'bruteforceability' for all end nodes.
    probs = [(end_node, bruteforce_prob(G, start_node, end_node)) for end_node in nodes]

    # Sort the result by brute-force likelihood:
    probs.sort(key=lambda t: t[1])

    # Slice off the least-likely nodes
    least_likely_prob = probs[0][1]
    least_likely = filter(lambda t: t[1] == least_likely_prob, probs)

    # If there's a choice, return the 'simplest' node
    # (the one with the least number of elements.)
    return min(least_likely, key=lambda t: len(t[0]))


# Determines which of the passed nodes is *greatest*
# 'distance' to reach from a starting node.
# > This is the max shortest path.
# > If there's a tie, return node with
#   least # of edges going into it (min in_degree).
def most_distant_node(G, start_node, nodes):
    # print('start ' + str(start_node))
    # print('leafs ' + str(nodes))
    # print('graph ' + str(G.nodes()) + ' | ' + str(G.edges()))

    # Get shortest paths from start_node to each node.
    paths = [nx.shortest_path(G, source=start_node, target=n) for n in nodes]

    # Select only the longest ones.
    longest_path_dist = max([len(p) for p in paths])
    longest_paths = filter(lambda p: len(p) == longest_path_dist, paths)

    # If there's multiple choices...
    if len(longest_paths) > 1:

        # Try to prune even further by choosing only those endpoints
        # with least # of edges going into them:
        min_in_degree = max(G.in_degree(p[-1]) for p in longest_paths)
        min_in_degree_paths = filter(lambda p: G.in_degree(p[-1]) == min_in_degree, longest_paths)

        # Return the node that's hardest to reach.
        # If there's more than one, return one at random.
        return random.choice(min_in_degree_paths)[-1]

    elif len(longest_paths) == 1:
        return longest_paths[0][-1]
    else:
        return None

# Converts a path like [1, 2, 3] to an edge list [ (1, 2), (2, 3) ].
def edges_from_path(path):
    if len(path) <= 1: return ()
    edges = []
    for idx, n in enumerate(path[:-1]):
        edges.append( (n, path[idx+1]) )
    return edges

def leafs_of_graph(G):
    return [x for x in G.nodes_iter() if (G.out_degree(x)==0 and G.in_degree(x) > 0)]
