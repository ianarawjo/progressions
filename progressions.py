# -*- coding: utf-8 -*-
import networkx as nx
from multiset import FrozenMultiset as Multiset
from itertools import permutations
import random

__DEBUG_PRINT = False
def log(x):
    if __DEBUG_PRINT:
        print(x)

flatten = lambda l: sum(l, [])
complexity = lambda state_tuple: state_tuple[1].number_of_edges()
without_omega = lambda l: (l.count('xxx') == 0) or (l.count('xxx') == 1 and l.count('xx') == 0)
leafs_of_graph = lambda G: [x for x in G.nodes_iter() if (G.out_degree(x)==0 and G.in_degree(x) > 0)]
irreducable = lambda a: any(x in a for x in ['_', '==', 'x'])
has_bool = lambda a: any(x in a for x in ['false', 'true'])
has_val = lambda a: any(x in a for x in ['A', 'B'])

def group_data(lst, key=(lambda x: x), sorter=None):
    vals = set(map(key, lst))
    if sorter: vals = sorter(vals)
    return [[y for y in lst if key(y) == v] for v in vals]

def edges_from_path(path):
    if len(path) <= 1: return ()
    edges = []
    for idx, n in enumerate(path[:-1]):
        edges.append( (n, path[idx+1]) )
    return edges

def cumulative_combine_sets(list_of_sets):
    rst = []
    prev = frozenset()
    for s in list_of_sets:
        new_s = s | prev # set union
        rst.append( new_s )
        prev = new_s
    return rst

# Calculate the probability of brute-forcing the given path.
# (i.e. by randomly choosing an out-edge at each node).
def bruteforce_prob_path(G, path):
    if len(path) == 2: return 1.0
    p = 1.0

    mid = path[:-1]
    for n in mid:
        # The probability of selecting the ‘correct’ edge
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

# Chooses a random multiset subset of a set,
# i.e. allowing duplicates when randomly choosing from the set.
# It's like picking one thing out of a hat and putting it
# back in before picking another thing.
def random_multi_subset(s, num_elements):
    return Multiset([random.choice(list(s)) for _ in xrange(num_elements)])

# Given all possible valid expressions, we
# can progressively select bounded subsets and sort
# them by 'complexity'.
def generateRandomStates(seed_exprs, num_exprs_choose=3, trials=20):
    prev_selections = []
    possible_states = [] # list of (start_state, state_graph) tuples
    while trials > 0:

        # Grab a random selection of valid expressions.
        random_exprs = random_multi_subset( seed_exprs, num_exprs_choose ) # with length 3...
        if random_exprs not in prev_selections and without_omega(list(random_exprs)):

            # Make sure we don't test this state again.
            prev_selections.append(random_exprs)

            # Split into board and toolbox combos.
            board_states = list(powerset(random_exprs))
            board_states = [Multiset(b) for b in board_states]
            toolbox_states = [(random_exprs - b) for b in board_states] # This is multiset differences, i.e. the remaining elements go into the toolbox.

            # Compute state graphs for all possible
            # game start states from the random_exprs:
            for i in xrange(len(board_states)):
                state = {
                    'board': board_states[i],
                    'toolbox': toolbox_states[i]
                }

                G = computeStateGraph( state )

                # First check if there's a reachable 'goal' (leaf of tree)
                # here that doesn't include a hole (_) or irreducable function:
                leafs = [str(M) for M in leafs_of_graph(G)] # this is a list of Multisets converted into strings.
                if all([irreducable(a) for a in leafs]):
                    # Every leaf has a hole or irreducable (e.g. a lambda). Skip this state.
                    continue

                # Add (state, graph) tuple to to list of possibilities.
                possible_states.append( (state, G) )

        trials -= 1

    return possible_states

# Preset starting values for testing.
# start_states = [
#     { 'board':[ "_ == _", "star" ],
#       'toolbox':[ "star", "rect" ] },
#     { 'board':[ "xx", "star" ],
#       'toolbox':[ "rect" ] }
# ]

# TODO: put in another file.
# Thanks to https://stackoverflow.com/a/1482320.
def powerset(s):
    x = len(s)
    masks = [1 << i for i in range(x)]
    for i in range(1 << x):
        yield [ss for mask, ss in zip(masks, s) if i & mask]

def concept(name, expr=None, reduction=None):
    args = "()"
    if expr != None:
        args = "(" + ",".join(expr) + ")"
    return name.upper() + args + ('->' + reduction) if reduction != None else ''

# Takes some expression x
# and the _rest_ of the expressions on the board, M.
def try_reduce(x, M):

    if '_' in x:
        # Replace (if possible) first _ in x with something in M...
        # TODO: Remove duplicates.

        # SPECIAL exclusion criteria: Don't let _ in == be replaced by 'true' or 'false'!
        return [((M - Multiset([n])) + Multiset([x.replace('_', n, 1)]), concept('fill', str(n))) for n in M if
                (not 'x' in n and not '==' in n and not 'true' in n and not 'false' in n)]
    elif '==' in x:
        # Reduce completed equality expression:
        # (parse out left and right side and reduce to true or false...)
        idx = x.find('==')
        p, q = x[:idx].strip(), x[(idx+2):].strip()
        if p == q:
            return [ (M + Multiset(['true']), concept('eq', (p, q), 'true')) ]
        else:
            return [ (M + Multiset(['false']), concept('eq', (p, q), 'false')) ]
    elif x == 'xxx':
        return [(M + Multiset([n]) + Multiset([n]), concept('triple', str(n))) for n in M if not (not('_' in x) and '==' in x)]
    elif x == 'xx':
        return [(M + Multiset([n]), concept('double', str(n))) for n in M if not (not('_' in x) and '==' in x)]
    elif x == 'x' and len(M) > 0:
        return [(M, concept('iden'))]
    else:
        return []

# Function (recursive) which a Multiset M (of states)
# and fills the DiGraph G of states.
def f(M, G):

    # Get set of all unique items
    S = set(M)

    for x in S:

        # Try to reduce item x given free items M - x (M excluding x)
        # > If it can reduce, returns a list of multisets.
        # > If it can't, return empty list.
        possible_new_states = try_reduce(x, M - Multiset([x]))

        for new_M, new_M_concept in possible_new_states:
            if new_M == M:
                continue

            # Check if new_M is in G.
            # > If new_M is in G:
            if new_M in G.nodes():
                # Add edge in G from M to new_M, then skip.
                G.add_edge(M, new_M, concept=new_M_concept)
                log('      added edge from ' + str(M) + ' to ' + str(new_M))
                continue

            # > Otherwise, add node n to end of g, then
            #   pass n and new_M to f.
            G.add_node(new_M)
            G.add_edge(M, new_M, concept=new_M_concept)

            log(' -- ' + str(M) + ' --> ' + str(new_M))

            f(new_M, G)

    return G

# Generate graph from {board, toolbox} game state:
def computeStateGraph(state):
    board = Multiset(state['board'])
    G = nx.DiGraph()
    G.add_node(board)
    toolbox = Multiset(state['toolbox']) if 'toolbox' in state else Multiset([])
    log("Computing graph for board " + str(board) + "...")
    toolbox_combinations = list(powerset( sorted(toolbox) ))
    for t in toolbox_combinations:
        root = board + Multiset(t)
        if root != board:

            # We need to be careful here. The
            # 'root' here can actually obscure
            # multiple toolbox-place events,
            # and multiple orders in which these placements can occur.
            # While it is fine that we assume all needed toolbox items are
            # chosen at round start (in practice this isn't often the case),
            # we can't assume that pulling out {A,B,C} is the same complexity
            # as pulling out {A} alone.
            if len(t) > 1:
                orderings = permutations(t)
                # For each ordering, generate a directed path in the graph:
                for permutation in orderings:
                    cumulative_sets = cumulative_combine_sets( [frozenset(n) for n in permutation] )
                    cumulative_sets = [ Multiset(s) for s in cumulative_sets ] # type conversion
                    G.add_edges_from(edges_from_path(cumulative_sets), concept='TOOLBOX_PLACE')
            else:
                G.add_node(root)
                G.add_edge(board, root, concept='TOOLBOX_PLACE')
        log(' -combination ' + str(t) + ':')
        f(root, G)
    return G

# Generate random sample of
# starting states of the game:
start_states = []

# All the high-level, most-abstract versions of expressions.
# e.g. all holes are empty.
abstract_exprs = ["_ == _", "A", "B", "xx", "xxx", "x"]

# Using the powerset of valid expressions,
# we can find all possible valid expressions.
# These are all valid starting values, technically speaking;
# it's nice not to have to write these manually.
abstract_states = list(powerset(abstract_exprs))
abstract_states = filter(without_omega, abstract_states) # Filter out states with multiple xxx's or the combo xxx and xx, because they wil expand indefinitely.

all_valid_exprs = set()
for a in abstract_states:
    ms = f(Multiset(a), nx.DiGraph()).nodes()
    exprs = flatten([list(m) for m in ms])
    all_valid_exprs.update(exprs)

# Generate a list of random (state, graph) pairs,
# representing possible levels and their traversals.
levels = generateRandomStates( all_valid_exprs, 1, 20 ) + \
         generateRandomStates( all_valid_exprs, 2, 20 ) + \
         generateRandomStates( all_valid_exprs, 3, 60 ) + \
         generateRandomStates( all_valid_exprs, 4, 80 )
        #  generateRandomStates( all_valid_exprs, 5, 60 )

# Order levels by complexity
# levels = sorted(levels, lambda A,B: complexity(A) - complexity(B))

# Output the resulting progression,
# sorted by bruteforceability:
progression = []
for l in levels:
    state, G = l
    possible_goals = filter(lambda M: not irreducable(str(M)) and (not has_bool(str(M)) or not has_val(str(M))), leafs_of_graph(G))
    if len(possible_goals) == 0: continue
    goal, likelihood = least_bruteforceable(G, Multiset(state['board']), possible_goals)
    progression.append( (state, G, goal, likelihood) )

levels = [] # Cleanup.
progression.sort(key=lambda t: (2.0 - t[3])) # Sort by likelihood of brute forcing the level.

# Now extract the 'trace concepts' (set of sequences of concepts used in all solution paths,
# [e.g. {ABC, EF, D} if there are 3 separate paths to solving the level)]
# of each graph G. Using the trace concepts we can generate a plausible
# directed acyclic graph (DAG) representing a concept dependency tree (from Erik's work).
def trace(state, G, goal):
    simplify = lambda s: s.split('(')[0] + (('->' + s.split('->')[1]) if '->' in s else '')
    all_concepts = []
    for path in nx.all_simple_paths(G, source=Multiset(state['board']), target=goal):
        all_concepts.append(frozenset([simplify(G[path[i]][path[i+1]]['concept']) for i in range(len(path)-1)]))
    return frozenset(all_concepts)

# Tack on 'trace concepts' onto the end of per-level data:
# * (see https://stackoverflow.com/a/4913789 for example)
progression = map(lambda tup: tup + (trace(tup[0], tup[1], tup[2]),), progression)

def flatten_traces(progression):
    # For now, just take a random trace:
    # (we could take the worst-case or best-case,
    # but this might not be consistently accurate)
    # (don't consider multiple paths)
    def convert(trace):
        if len(trace) > 1:
            return random.choice(list(trace))
        elif len(trace) == 1:
            return list(trace)[0]
        else:
            return frozenset()

    return list(map(lambda tup: tup[:4] + (convert(tup[4]),), progression))

'''
So there's two ways to actually do the partial ordering.
At the high-level we want to bucket levels by concepts we want to teach
-- for that we don't even need a DAG, b.c. for 2 concepts {A, B},
we can just bucket by {A, B, AB} (the powerset). Then, WITHIN each bucket,
we can perform the proper partial ordering sort... BUT! We can
also sort by bruteforce probability... It is unclear which is better.

So for the partial_ordering function,
we will just return the levels bucketed by
the powerset of those concepts, in a topological order.

If, however, we want a full_graph_partial_ordering,
we will perform a per-level partial ordering
and return the topological sort of that ordering,
where all concepts (moves) are under consideration.
'''

# Now construct a partial ordering graph on the graphs:
# (e.g. conceptsToTeach = ('EQ->true', 'EQ->false') for Boolean chapter)
def partial_ordering(progression, conceptsToTeach):

    levels = flatten_traces(progression)

    # Throw out all the levels that don't contain
    # any of the concepts we want to teach:
    only_relevant_concepts = lambda concepts: frozenset(filter(lambda c:(c in conceptsToTeach), concepts))
    is_relevant = lambda concepts: len(only_relevant_concepts(concepts)) > 0
    progression = list(filter(lambda tup: is_relevant(tup[4]), progression))

    concept_ordering = list([frozenset(lst) for lst in powerset(conceptsToTeach)])[1:] # exclude empty set {} at idx 0
    concept_ordering.sort(key=lambda x:len(x))
    buckets = []

    # This should start with the 'most complex' traces
    # first. For instance, if conceptsToTeach = {A, B, C},
    # then this starts with {ABC}.
    for c in reversed(concept_ordering):

        # Filter-remove over levels:
        def F(tup):
            return c.issubset(frozenset(tup[4]))
        levels_containing_only_c = list(filter(F, levels))
        buckets.append( (c, levels_containing_only_c) )


        # Remove levels containing concepts C from consideration
        levels = list(filter(lambda tup: not F(tup), levels))

    # Return progression bucketed by concepts in form:
    # (concept trace, level desc)
    return list(reversed(buckets))

# So now we can ask it to give us a progression to
# 'teach' Boolean reductions:
for lvl in progression:
    print(lvl[4])
buckets = partial_ordering(progression, ('EQ->true', 'EQ->false'))

# ... and this should return a list like
#   ({'EQ->true'}, levels containing just that ->true),
#   ({'EQ->false'}, levels containing just ->false),
#   ({'EQ->true', 'EQ->false'}, levels containing both ->true and ->false reductions)
# We can sort the levels within this list by their "concept-relative" BFP (brute force probability):
def concept_relative_BFP(lvl, indiv_concept):

    simplify = lambda s: s.split('(')[0] + (('->' + s.split('->')[1]) if '->' in s else '')

    # First, find on what edge(s) the concept appears
    # as a 'move' in this level, and take the state it goes to.
    G = lvl[1]
    start_state = Multiset(lvl[0]['board'])
    cs = dict(nx.get_edge_attributes(G, 'concept'))
    BFPs = []
    for from_node, to_node in cs:
        val = simplify( cs[from_node, to_node] )
        if indiv_concept == val:
            BFPs.append(bruteforce_prob(G, start_state, to_node))

    # Now return the *highest* BFP
    # (e.g. concept 'A' could appear in the first edge of the graph with BFP=1.0,
    # and then appear later with BFP=0.0001, but we're ignoring the harder paths for now.)
    return max(BFPs)
def concepts_relative_BFP(lvl, concepts):
    bfps = list(map(lambda c:concept_relative_BFP(lvl, c), concepts))
    return reduce(lambda x,y:x*y, bfps)

# Total 'complexity' = likelihood of solving * product( concept-relative-BFP's ) / length_of_optimal_trace
buckets_by_rel_BFP = [(b[0], sorted(b[1], key=lambda lvl: 2.0- lvl[3] * concepts_relative_BFP(lvl, b[0]) / len(lvl[4]))) for b in buckets]

# Now re-flatten this list into a final progression (list of levels):
progression = flatten([b[1] for b in buckets_by_rel_BFP])

# We can then topological sort the DAG (which is a graph-of-graphs)
# to generate a plausible progression. Within this sort,
# we want to sub-sort (and cull) such that the BFP (brute force probability) of completing
# the levels increases over time. That is the overall goal. Within that, even,
# we want the BFP _per concept_ to increase over time since it is introduced.
# (We assume we start with 'known' concepts C,D,E for instance and 'new' concepts A,B that we'd like to teach.)
# In other words, to introduce concept A (which could be how to get 'false' from ==),
# we'd like the initial BFP(A)=1.0 (easiest) and the BFP of the graph that includes A
# to be as low as possible, relative to its placement in the progression.
# (Initially this would also be BFP(G)=1.0; which actually models the first level of the Boolean chapter).
# Then the BFP(A) should increase as much as possible before introducing, say, new concept B...
# because minimizing simultaneously BFP(A)|BFP(B) is what we actually want (?)... Minimizing this
# value by the end of the progression would result in a level using all _new_ concepts at
# a relatively complex difficulty (relative to the new concepts).

for lvl in progression:
    state, G, goal, likelihood, trace_concepts = lvl
    print( '%-48s%-48sp: %-22.6f%-12s' % (str(state['board']), str(state['toolbox']), likelihood, ':goal ' + str(goal)))
# # Run root cases:
# graphs = []
# for state in start_states:
#     G = computeStateGraph( state )
#     graphs.append(G)
#     log("\nFinal graph:")
#     log(G.nodes())
#     log("\n")
#

def full_graph_partial_ordering(progression):

    # Take trace concepts at random for levels
    # with more than one trace (solution path)...
    levels = flatten_traces(progression)
    concept_covers = lambda c1, c2: c1.issuperset(c2)

    # Add all the levels to a graph as single nodes indexed by their initial states:
    DAG = nx.DiGraph()
    for lvl in levels:
        DAG.add_node(str(lvl[0]), data=lvl)

    # Bucket the progression by # of concepts in the traces:
    # (this is sorted in increasing order)
    buckets = group_data(progression, key=lambda tup:len(tup[4]), \
                                   sorter=lambda vals:sorted(list(vals)))

    # Do 'bottom-up' partial ordering
    # ('top-down' would start from the highest # of concepts
    # but this would search a powerset with combinations that
    # may not actually occur in the data)... So we can
    # start from the 'smallest' levels, concept-wise,
    # and see if those concepts are included in levels with +n concepts (n>0).
    for idx, b in enumerate(buckets[:-1]):
        for lvl in b:
            lvl_concepts = lvl[4]
            for other_b in buckets[idx+1:]: # Only iterate through levels with more concepts than 'lvl'
                for other_lvl in other_b:
                    other_lvl_concepts = other_lvl[4]
                    # If one concept trace 'covers' (as in, includes) another,
                    # then 'lvl' comes before 'other_lvl' in the partial ordering of concepts.
                    # For instance, {A, B} includes {A}.
                    if concept_covers(other_lvl_concepts, lvl_concepts):
                        # Add a directed edge from lvl to other_lvl:
                        DAG.add_edge(str(lvl[0]), str(other_lvl[0]))

    # Topological sort the partial ordering graph
    node_ordering = nx.topological_sort(DAG) # this gives us the toposort as a list of node indices
    return [DAG.node[n]['data'] for n in node_ordering] # the data for each node are the level specs...
