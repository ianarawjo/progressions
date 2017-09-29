from __future__ import print_function # this makes print(*args) work

from multiset import FrozenMultiset as Multiset
import networkx as nx
import state_graph as sg
from graph_util import least_bruteforceable, leafs_of_graph
from semantics import irreducable

# Debug log
__DEBUG_PRINT = False
def log(*args):
    if __DEBUG_PRINT:
        print(*args)

class Level:
    def __init__(self, start_state):
        self.state = start_state
        self.G = None
        self.goal = None
        self.bfp = None
        self.trace_concepts = None
        self.invalid = False

    def compute_state_graph(self):
        if not self.state:
            log('Error: No start state in Level.')
            return
        elif not isinstance(self.state, dict):
            log('Error: Level state is not dict.', self.state)
            return

        self.G = sg.compute(self.state)

    def pick_goal(self, filterFunc=None):
        if not self.G:
            log('Error: No state graph has been computed for this Level. Try calling computeSemanticGraph first.')
            return

        #possible_goals = filter(lambda M: not irreducable(str(M)) and (not has_bool(str(M)) or not has_val(str(M))), leafs_of_graph(G))
        G = self.G
        state = self.state
        possible_goals = filter(lambda M: not irreducable(str(M)), leafs_of_graph(G))
        if filterFunc != None: possible_goals = filter(lambda M: filterFunc(str(M)), possible_goals)

        if len(possible_goals) == 0:
            log('Warning: No valid goal for this level.')
            log(leafs_of_graph(G))
            self.invalid = True
            return

        goal, likelihood = least_bruteforceable(G, state['board'], possible_goals)

        self.goal = goal # goal is a Multiset
        self.bfp = likelihood # brute force probability
        self.trace_concepts = sg.get_trace_concepts(self.state, self.G, self.goal) # set of concepts in the solution path(s) to the chosen goal

        if len(self.trace_concepts) == 0:
            log('Warning: No trace concepts for level', self.state, self.goal, self.G.nodes())
            self.invalid = True

    def __str__(self):
        if self.bfp == None:
            return '%-48s%-48sp: %-22s%-12s' % (str(self.state['board']), str(self.state['toolbox']), 'ERROR', ':goal ' + str(self.goal))
        else:
            return '%-48s%-48sp: %-22.6f%-12s' % (str(self.state['board']), str(self.state['toolbox']), self.bfp, ':goal ' + str(self.goal))
