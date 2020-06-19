import time
# math
import numpy as np
# graph
import networkx as nx
# lib
from wadl.lib.utils import *
# solver
import z3


class SATproblem(object):
    """docstring for SATSolver"""
    def __init__(self, graph, limit, starts=None):
        # unpack
        self.graph = graph
        self.nodes = list(self.graph.nodes)
        self.limit = limit
        self.starts = starts if starts is not None else [self.nodes[0]]

        # get sizes
        self.nNode = len(self.graph)
        self.nPath = len(self.starts)
        # form problem instance
        self.z3 = z3.Solver()
        self.make()

    def make(self):
        self.satVars = self.makeVars(self.nNode, self.nPath, self.limit)

        # create blist and for them to be false
        bList = self.L1Prune(self.graph, self.satVars, self.starts)
        self.removeVars(bList)

        self.nVar = self.satVars.size
        self.nRmv = len(bList)
        self.makeConts(self.graph, self.satVars, self.starts)

        print(f"Built problem with {self.nVar-self.nRmv} vars, {self.nRmv} removed")

    def makeVars(self, nNode, nPath, limit):
        # makes a bool var for each space, time, robot tuple
        satVars=([[[z3.Bool("x%s_t%s_s%s" % (i, t, s))
                    for s in range(nNode)]
                    for t in range(limit)]
                    for i in range(nPath)])
        nVars = nNode * nPath *limit
        return np.array(satVars)

    def L1Prune(self, graph, satVars, starts):
        bList = []
        # force to false a subset of the variables.
        for i, start in enumerate(starts):
            print(start)
            # convert base to world point
            # print(worldBase)
            for si, s in enumerate(graph):
                # reachable prune
                worldDist = l1(start, s) # l1 distance between two pts
                for t in range(worldDist):
                    if t < 2:
                        continue
                    # not forward reachable from  start
                    bList.append(satVars[i][t][si])
                    # not backward reachable from end
                    bList.append(satVars[i][-1-t][si])

        return bList

    def removeVars(self, bList):
        for boolVar in bList:
            self.z3.add(z3.Not(boolVar))
    

    def makeConts(self, graph, satVars, starts):
        # sets the constraints for the problem
        # running constraints
        T = nx.adjacency_matrix(graph)
        nPath = len(satVars)
        limit = len(satVars[0])

        for i in range(self.nPath):
            # for each agent
            for t in range(limit):
                # one spot per time
                self.exactlyOne(self.z3, satVars[i][t])
                # movement
                if t+1 == limit:
                    # ignore the last bit for the end
                    break
                for si, s in enumerate(graph):
                    nextMoves = [satVars[i][t+1][ssi]
                                 for ssi, ss in enumerate(graph)
                                 if T[si, ssi] == 1 ]
                    # add self loop if it's the start or end node
                    if s == starts[i]:
                        nextMoves.append(satVars[i][t+1][si])
                    # add constraint 
                    self.z3.add(z3.Or(z3.Not(satVars[i][t][si]), *nextMoves))
        # for all agent and times each space must be true at least once
        for si, s in enumerate(graph):
            tempList = []
            for i in range(nPath):
                tempList.extend([satVars[i][t][si] for t in range(limit)])

            self.atLeastOne(self.z3, tempList)
        # boundary constants
        for i, start  in enumerate(starts):
            startIdx = self.graph.nodes[start]['index']
            self.z3.add(z3.And(satVars[i][0][startIdx],
                               satVars[i][-1][startIdx]))

    def solve(self):
        # solve the problem
        startTime = time.time()
        solTime = None
        if self.z3.check() == z3.sat:
            solTime = (time.time()-startTime)/60.
            print("Solution Found: {:2.5f} min".format(solTime))
            return True, self.output(), solTime
        else:
            raise RuntimeError("I will never be satisfiiiiied")
            return False, None, solTime



    def atMostOne(self, problem, varList):
        # constrains at most one of the vars in the list to be true
        problem.add(z3.PbLe([(v, 1) for v in varList], 1))

    def atLeastOne(self, problem, varList):
        # constrains at least one of the vars in the list to be true
        problem.add(z3.PbGe([(v, 1) for v in varList], 1))

    def exactlyOne(self, problem, varList):
        # constrains at exactly one of the vars in the list to be true
        problem.add(z3.PbEq([(v, 1) for v in varList], 1))


    def output(self):
        m = self.z3.model()
        # colors = ['b', 'g', 'r', 'm']
        nPath, limit, nNode = self.satVars.shape
        paths = []
        for i in range(nPath):
            path = []
            for t in range(limit):
                for si, s in enumerate(self.graph.nodes):
                    # print(i, t, s)
                    # print(m.evaluate(self.satVars[i][t][s]))
                    if m.evaluate(self.satVars[i][t][si]):
                        path.append(s)

            # store the path
            paths.append(path)
        return paths


