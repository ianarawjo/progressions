# -*- coding: utf-8 -*-
import networkx as nx
from multiset import FrozenMultiset as Multiset
import random
import state_graph as sg
from level import Level

# Project modules
from semantics import concept, try_reduce, without_omega, irreducable, simplify
from set_util import powerset, random_multi_subset, cumulative_combine_sets
from graph_util import bruteforce_prob, bruteforce_prob_path, least_bruteforceable, edges_from_path, leafs_of_graph, print_graph

flatten = lambda l: sum(l, [])
complexity = lambda state_tuple: state_tuple[1].number_of_edges()
has_bool = lambda a: any(x in a for x in ['false', 'true'])
has_val = lambda a: any(x in a for x in ['A', 'B'])

def group_data(lst, key=(lambda x: x), sorter=None):
    vals = set(map(key, lst))
    if sorter: vals = sorter(vals)
    return [[y for y in lst if key(y) == v] for v in vals]

# Preset starting values for testing.
# start_states = [
#     { 'board':[ "_ == _", "star" ],
#       'toolbox':[ "star", "rect" ] },
#     { 'board':[ "xx", "star" ],
#       'toolbox':[ "rect" ] }
# ]

# Generate random sample of
# starting states of the game:
start_states = []

all_valid_exprs = sg.gen_all_valid_exprs()

# Generate a list of random (state, graph) pairs,
# representing possible levels and their traversals.
random_states = sg.gen_random_states( all_valid_exprs, 1, 40 ) + \
                sg.gen_random_states( all_valid_exprs, 2, 40 ) + \
                sg.gen_random_states( all_valid_exprs, 3, 60 )
                # sg.gen_random_states( all_valid_exprs, 4, 80 )
                #  sg.gen_random_states( all_valid_exprs, 5, 60 )

# Convert to levels
progression = [Level(state) for state, _ in random_states]

# Compute state graph and goals for each level:
for lvl in progression:
    lvl.compute_state_graph()
    lvl.pick_goal(lambda s: (not has_bool(s) or not has_val(s)))

# Remove invalid levels.
# TODO: Figure out why some levels have to trace_concepts...
# for lvl in progression:
#     if lvl.invalid == True:
#         print(lvl)
#         # print_graph(lvl.G)
#         # break
# exit(0)

progression = filter(lambda lvl: lvl.invalid == False, progression)

# for lvl in progression:
#     print(lvl)
    # print_graph(lvl.G)
    # break
# exit(0)

# Sort levels by (decreasing) likelihood of brute forcing the level:
progression.sort(key=lambda lvl: (2.0 - lvl.bfp))

def flatten_traces(progression):
    # For now, just take a random trace:
    # (we could take the worst-case or best-case,
    # but this might not be consistently accurate)
    # (don't consider multiple paths)
    def flat(trace):
        return random.choice(list(trace))

    for lvl in progression:
        if len(lvl.trace_concepts) >= 1:
            lvl.trace_concepts = flat(lvl.trace_concepts)

    return progression

# Now construct a partial ordering graph on the graphs:
# (e.g. conceptsToTeach = ('EQ->true', 'EQ->false') for Boolean chapter)
# This should return a list like
#   ({'EQ->true'}, levels containing just that ->true),
#   ({'EQ->false'}, levels containing just ->false),
#   ({'EQ->true', 'EQ->false'}, levels containing both ->true and ->false reductions)
# We can sort the levels within this list by their "concept-relative" BFP (brute force probability):
def partial_ordering(progression, conceptsToTeach):

    levels = list(flatten_traces(progression))

    # Throw out all the levels that don't contain
    # any of the concepts we want to teach:
    def only_relevant_concepts(concepts):
        x = frozenset(filter(lambda c:(c in conceptsToTeach), concepts))
        # print(concepts, conceptsToTeach, x)
        return x
    is_relevant = lambda concepts: len(only_relevant_concepts(concepts)) > 0
    progression = list(filter(lambda lvl: is_relevant(list(lvl.trace_concepts)[0]), progression))

    concept_ordering = list([frozenset(lst) for lst in powerset(conceptsToTeach)])[1:] # exclude empty set {} at idx 0
    concept_ordering.sort(key=lambda x:len(x))
    buckets = []

    # This should start with the 'most complex' traces
    # first. For instance, if conceptsToTeach = {A, B, C},
    # then this starts with {ABC}.
    for c in reversed(concept_ordering):

        # Filter-remove over levels:
        def F(lvl):
            return c.issubset(lvl.trace_concepts)

        levels_containing_only_c = list(filter(F, levels))

        buckets.append( (c, levels_containing_only_c) )

        # Remove levels containing concepts C from consideration
        levels = list(filter(lambda lvl: not F(lvl), levels))

    # Return progression bucketed by concepts in form:
    # (concept trace, level desc)
    return list(reversed(buckets))

# So now we can ask it to give us a progression to
# 'teach' Boolean reductions:
buckets = partial_ordering(progression, ('EQ->true', 'EQ->false'))

# Total 'complexity' = likelihood of solving * product( concept-relative-BFP's ) / length_of_optimal_trace
def lvl_complexity(lvl):
    return 2.0 - lvl.bfp * sg.concepts_relative_BFP(lvl, b[0]) / len(list(lvl.trace_concepts)[0])

# Sort levels in each bucket by complexity:
buckets_by_rel_BFP = [(b[0], sorted(b[1], key=lvl_complexity)) for b in buckets]

# Now re-flatten this list into a final progression (list of levels):
progression = flatten([b[1] for b in buckets_by_rel_BFP])

# Print the final progression to console in a table:
for lvl in progression:
    print( '%-48s%-48sp: %-22.6f%-12s' % (str(lvl.state['board']), str(lvl.state['toolbox']), lvl.bfp, ':goal ' + str(lvl.goal)))
    if lvl.bfp > 1.0:
        print_graph(lvl.G)
        for path in nx.all_simple_paths(lvl.G, source=lvl.state['board'], target=lvl.goal):
            print(bruteforce_prob_path(lvl.G, path))

# FOR FUTURE USE (maybe)
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
