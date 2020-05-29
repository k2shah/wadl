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

    def solve(self):
        raise NotImplementedError

    def readSolution(self):
        raise NotImplementedError

class SATSolver(Solver):
    """docstring for SATSolver"""
    def __init__(self, maze):
        super(SATSolver, self).__init__(maze)
        self.problem = z3.Solver()
        self.satVars = []
        self.makeVars()
        self.findBlackList()

        print(f"Built problem with {self.nVar-self.nRmv} vars, {self.nRmv} removed")
        self.setConts()



    def makeVars(self):
        # makes a bool var for each space, time, robot tuple
        for i in range(self.maze.nAgent):
            # for each agent
            self.satVars.append([[z3.Bool("x%s_t%s_s%s" % (i, t, s))
                                for s in range(self.maze.nNode)]
                                for t in range(self.maze.limit)])
        self.nVar = \
            self.maze.nAgent * \
            self.maze.nNode * \
            self.maze.limit

    def findBlackList(self):
        self.blackList = []
        # force to false a subset of the variables.
        for i in range(self.maze.nAgent):
            start = self.maze.globalStarts[i]
            # convert base to world point
            # print(worldBase)
            for si, s in enumerate(self.maze.graph):
                # reachable prune
                worldDist = l1(start, s) # l1 distance between two pts
                for t in range(worldDist):
                    if t < 2:
                        continue
                    # not forward reachable from  start
                    self.blackList.append(self.satVars[i][t][si])
                    # not backward reachable from end
                    self.blackList.append(self.satVars[i][-1-t][si])

        for boolVar in self.blackList:
            self.problem.add(z3.Not(boolVar))
        self.nRmv = len(self.blackList)

    def setConts(self):
        # sets the constraints for the problem
        # running constraints
        T = nx.adjacency_matrix(self.maze.graph)
        for i in range(self.maze.nAgent):
            # for each agent
            for t in range(self.maze.limit):
                # one spot per time
                self.exactlyOne(self.satVars[i][t])
                # movement
                if t+1 == self.maze.limit:
                    # ignore the last bit for the end
                    break
                for si, s in enumerate(self.maze.graph):
                    nextMoves = [self.satVars[i][t+1][ssi]
                                 for ssi, ss in enumerate(self.maze.graph)
                                 if T[si, ssi] == 1 ]
                    # add self loop if it's the start or end node
                    if s == self.maze.globalStarts[i]:
                        nextMoves.append(self.satVars[i][t+1][si])
                    # add constraint 
                    self.problem.add(z3.Or(z3.Not(self.satVars[i][t][si]),
                                           *nextMoves))
        # for all agent and times each space must be true at least once
        for si, s in enumerate(self.maze.graph):
            tempList = []
            for i in range(self.maze.nAgent):
                tempList.extend([self.satVars[i][t][si]
                                for t in range(self.maze.limit)])

            self.atLeastOne(tempList)
        # boundary constants
        for i in range(self.maze.nAgent):
            start = self.maze.globalStarts[i]
            startIdx = self.maze.graph.nodes[start]['index']
            self.problem.add(z3.And(
                             self.satVars[i][0][startIdx],
                             self.satVars[i][-1][startIdx]))

    def solve(self):
        # solve the problem
        startTime = time.time()
        if self.problem.check() == z3.sat:
            solTime = (time.time()-startTime)/60.
            self.maze.setSolTime(solTime)
            print("Solution Found: {:2.5f} min".format(solTime))
            return True, self.readSolution()
        else:
            raise RuntimeError("I will never be satisfiiiiied")
            return False, None



    def atMostOne(self, varList):
        # constrains at most one of the vars in the list to be true
        self.problem.add(z3.PbLe([(v, 1) for v in varList], 1))

    def atLeastOne(self, varList):
        # constrains at least one of the vars in the list to be true
        self.problem.add(z3.PbGe([(v, 1) for v in varList], 1))

    def exactlyOne(self, varList):
        # constrains at exactly one of the vars in the list to be true
        self.problem.add(z3.PbEq([(v, 1) for v in varList], 1))


    def readSolution(self):
        m = self.problem.model()
        # colors = ['b', 'g', 'r', 'm']
        # agents = [Agent(ID, self.maze, color=color)
        #           for ID, color in zip(range(self.maze.nAgent), colors)]
        paths = []
        for i in range(self.maze.nAgent):
            path = []
            for t in range(self.maze.limit):
                for si, s in enumerate(self.maze.graph.nodes):
                    # print(i, t, s)
                    # print(m.evaluate(self.satVars[i][t][s]))
                    if m.evaluate(self.satVars[i][t][si]):
                        path.append(s)

            # store the path
            paths.append(path)
        return paths