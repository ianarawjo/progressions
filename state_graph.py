from multiset import FrozenMultiset as Multiset
import networkx as nx
from itertools import permutations

# Project modules
from semantics import try_reduce, without_omega, irreducable, simplify
from set_util import random_multi_subset, powerset, cumulative_combine_sets
from graph_util import leafs_of_graph, bruteforce_prob, edges_from_path

flatten = lambda l: sum(l, [])

# Debug log
__DEBUG_PRINT = False
def log(x):
    if __DEBUG_PRINT:
        print(x)

# Function (recursive) which a Multiset M (of states)
# and fills the DiGraph G of states.
def f(M, G):

    # Get set of all unique items
    S = frozenset(M)

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
def compute(state):

    board = state['board']
    G = nx.DiGraph()
    G.add_node(board)

    toolbox = state['toolbox'] if 'toolbox' in state else Multiset([])
    toolbox_combinations = list(powerset( sorted(toolbox) ))

    log("Computing graph for board " + str(board) + "...")

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
                    cumulative_sets = cumulative_combine_sets( [Multiset([n]) for n in permutation] )
                    cumulative_sets = [ (Multiset(list(frzset)) + board) for frzset in cumulative_sets ] # type conversion
                    for M in cumulative_sets:
                        if not G.has_node(M):
                            G.add_node(M)

                    if edges_from_path(cumulative_sets)[-1][1] != root:
                        print('ERROR: Mismatch between root and edge', t, permutation)

                    G.add_edge(board, cumulative_sets[0], concept='TOOLBOX_PLACE()')
                    G.add_edges_from(edges_from_path(cumulative_sets), concept='TOOLBOX_PLACE()')
            else:
                G.add_node(root)
                G.add_edge(board, root, concept='TOOLBOX_PLACE()')

        log(' -combination ' + str(t) + ':')
        f(root, G)
    return G

def gen_all_valid_exprs():

    # All the high-level, most-abstract versions of expressions.
    # e.g. all holes are empty.
    base_exprs = ["_ == _", "A", "B", "xx", "xxx", "x"]

    # Using the powerset of valid expressions,
    # we can find all possible valid expressions.
    # These are all valid starting values, technically speaking;
    # it's nice not to have to write these manually.
    states = filter(without_omega, list(powerset(base_exprs)))  # Filter out states with multiple xxx's or the combo xxx and xx, because they wil expand indefinitely.
    all_valid_exprs = set()
    for a in states:
        ms = f(Multiset(a), nx.DiGraph()).nodes()
        es = flatten([list(m) for m in ms])
        all_valid_exprs.update(es)

    return all_valid_exprs

# Given all possible valid expressions, we
# can progressively select bounded subsets and sort
# them by 'complexity'.
def gen_random_states(seed_exprs, num_exprs_choose=3, trials=20):
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

                G = compute( state )

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

# Extracts the 'trace concepts' (set of sequences of concepts used in all solution paths,
# [e.g. {ABC, EF, D} if there are 3 separate paths to solving the level)]
# of each graph G. Using the trace concepts we can generate a plausible
# directed acyclic graph (DAG) representing a concept dependency tree (from Erik's work).
def get_trace_concepts(state, G, goal):
    all_concepts = []
    # print(' --> path ', state['board'], goal)
    for path in nx.all_simple_paths(G, source=state['board'], target=goal):
        all_concepts.append(frozenset([simplify(G[path[i]][path[i+1]]['concept']) for i in range(len(path)-1)]))
    return frozenset(all_concepts)

def concept_relative_BFP(lvl, indiv_concept):

    # First, find on what edge(s) the concept appears
    # as a 'move' in this level, and take the state it goes to.
    G = lvl.G
    start_state = Multiset(lvl.state['board'])
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
