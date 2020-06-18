#!/usr/bin/python3
import warnings as warn
import os
import sys
import time
# math
import numpy as np
import numpy.linalg as la
import numpy.random as rand
#graph 
import networkx as nx
# plot
import matplotlib.pyplot as plt
# lib
from wadl.lib.utils import *
# solver
import z3
z3.set_param('parallel.enable', True)
# z3.set_param('verbose', 1)

class Solver(object):
    """docstring for Solver"""
    def __init__(self, maze):
        self.maze = maze
        self.setup()

    def setup(self):
        raise NotImplementedError

    def solve(self):
        '''
        if solution is found return 
        return True, self.output() 
        else
        return False, None
        '''
        raise NotImplementedError



class SATSolver(Solver):
    """docstring for SATSolver"""
    def __init__(self, maze):
        super(SATSolver, self).__init__(maze)

    def setup(self):
        self.problem = z3.Solver()
        self.satVars = self.makeVars(self.maze.nNode,
                                self.maze.nAgent,
                                self.maze.limit)


        print(self.satVars.shape)
        # create blist and for them to be false
        bList = self.L1Prune(self.maze.graph, self.satVars, self.maze.globalStarts)
        self.removeVars(self.problem, bList)

        self.nVar = len(self.satVars)
        self.nRmv = len(bList)
        self.makeConts(self.problem, self.maze.graph, self.satVars, self.maze.globalStarts)

        print(f"Built problem with {self.nVar-self.nRmv} vars, {self.nRmv} removed")





    def makeVars(self, nNode, nAgent, limit):
        # makes a bool var for each space, time, robot tuple
        satVars=([[[z3.Bool("x%s_t%s_s%s" % (i, t, s))
                    for s in range(nNode)]
                    for t in range(limit)]
                    for i in range(nAgent)])
        nVars = nNode * nAgent *limit
        return np.array(satVars)

    def L1Prune(self, graph, satVars, starts):
        bList = []
        # force to false a subset of the variables.
        for i, start in enumerate(starts):
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

    def removeVars(self, problem, bList):
        for boolVar in bList:
            problem.add(z3.Not(boolVar))
    

    def makeConts(self, problem, graph, satVars, starts):
        # sets the constraints for the problem
        # running constraints
        T = nx.adjacency_matrix(graph)
        nAgent = len(satVars)
        limit = len(satVars[0])

        for i in range(self.maze.nAgent):
            # for each agent
            for t in range(limit):
                # one spot per time
                self.exactlyOne(problem, satVars[i][t])
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
                    problem.add(z3.Or(z3.Not(satVars[i][t][si]), *nextMoves))
        # for all agent and times each space must be true at least once
        for si, s in enumerate(graph):
            tempList = []
            for i in range(nAgent):
                tempList.extend([satVars[i][t][si] for t in range(limit)])

            self.atLeastOne(problem, tempList)
        # boundary constants
        for i, start  in enumerate(starts):
            startIdx = self.maze.graph.nodes[start]['index']
            problem.add(z3.And(satVars[i][0][startIdx],
                               satVars[i][-1][startIdx]))

    def solve(self):
        # solve the problem
        startTime = time.time()
        solTime = None
        if self.problem.check() == z3.sat:
            solTime = (time.time()-startTime)/60.
            self.maze.setSolTime(solTime)
            print("Solution Found: {:2.5f} min".format(solTime))
            return True, self.output()
        else:
            raise RuntimeError("I will never be satisfiiiiied")
            return False, None



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
        m = self.problem.model()
        # colors = ['b', 'g', 'r', 'm']
        nAgent, limit, nNode = self.satVars.shape
        paths = []
        for i in range(nAgent):
            path = []
            for t in range(limit):
                for si, s in enumerate(self.maze.graph.nodes):
                    # print(i, t, s)
                    # print(m.evaluate(self.satVars[i][t][s]))
                    if m.evaluate(self.satVars[i][t][si]):
                        path.append(s)

            # store the path
            paths.append(path)
        return paths