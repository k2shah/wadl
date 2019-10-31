#!/usr/bin/python3
import warnings as warn
import os
import sys
import time
# math
import numpy as np
import numpy.linalg as la
import numpy.random as rand
# plot
import matplotlib.pyplot as plt
# lib
from lib.agent import Agent
from lib.capeConfig import CrozConfig, RookConfig, RoydsConfig
from lib.utils import *
# solver
import z3


class SAT(object):
    """docstring for SAT"""
    def __init__(self, config):
        self.problem = z3.Solver()
        self.config = config
        self.satVars = []
        self.makeVars()
        self.setConts()

    def makeVars(self):
        # makes a bool var for each space, time, robot tuple
        for i in range(self.config.nAgent):
            # for each agent
            self.satVars.append([[z3.Bool("x%s_t%s_s%s" % (i, t, s))
                                for s in range(len(self.config.stateSpace))]
                                for t in range(self.config.maxTime)])
            # print(self.satVars[0][0])

    def setConts(self):
        # sets the constraints for the problem
        # running constraints
        for i in range(self.config.nAgent):
            # for each agent
            for t in range(self.config.maxTime):
                # one spot per time
                self.exactlyOne(self.satVars[i][t])
                # movement
                if t+1 == self.config.maxTime:
                    # ignore the last bit for the end
                    break
                for s in range(len(self.config.stateSpace)):
                    nextMoves = [self.satVars[i][t+1][ss]
                                 for ss in range(len(self.config.stateSpace))
                                 if self.config.Ts[s, ss]]
                    self.problem.add(z3.Or(
                                     z3.Not(self.satVars[i][t][s]),
                                     *nextMoves))
        # for all agent and times each space must be true at least once
        for s in range(len(self.config.stateSpace)):
            tempList = []
            for i in range(self.config.nAgent):
                tempList.extend([self.satVars[i][t][s]
                                for t in range(self.config.maxTime)])

            self.atLeastOne(tempList)
        # boundary constants
        for i in range(self.config.nAgent):
            agentInit = self.config.initAgent[i]
            self.problem.add(z3.And(
                             self.satVars[i][0][agentInit],
                             self.satVars[i][-1][agentInit]))

    def solve(self):
        # solve the problem
        z3.set_param('parallel.enable', True)
        z3.set_param('verbose', 1)
        if self.problem.check() == z3.sat:
            print("Solution Found")
        else:
            raise RuntimeError("I will never be satisfiiiiied")

    def readSolution(self):
        m = self.problem.model()
        colors = ['b', 'g', 'r', 'm']
        agents = [Agent(ID, self.config, color=color)
                  for ID, color in zip(range(self.config.nAgent), colors)]

        for i in range(self.config.nAgent):
            path = []
            for t in range(self.config.maxTime):
                for s in range(len(self.config.stateSpace)):
                    # print(i, t, s)
                    # print(m.evaluate(self.satVars[i][t][s]))
                    if m.evaluate(self.satVars[i][t][s]):
                        path.append(s)
            # print(path)
            agents[i].makeTrajectory(path)
        return agents

    def atMostOne(self, varList):
        # constrains at most one of the vars in the list to be true
        self.problem.add(z3.PbLe([(v, 1) for v in varList], 1))

    def atLeastOne(self, varList):
        # constrains at least one of the vars in the list to be true
        self.problem.add(z3.PbGe([(v, 1) for v in varList], 1))

    def exactlyOne(self, varList):
        # constrains at exactly one of the vars in the list to be true
        self.problem.add(z3.PbEq([(v, 1) for v in varList], 1))


def main(outDir):
    # agent parameters
    agentParameters = {}

    # zone 0
    agentParameters["base"] = 11
    agentParameters["maxTime"] = 55
    agentParameters["initPos"] = [10, 21]
    nAgent = len(agentParameters["initPos"])

    # gen parameters
    step = 40
    zone = 0
    ver = 1
    # input files
    # croz west
    config = CrozConfig(agentParameters,
                        step=step, zone=zone,
                        prefix=True)
    # crox east
    # config = RoydsConfig(file, agentParameters, step=step)

    outDir += '_sat_' + str(step) + '_n' + str(nAgent) + '_z' + str(zone)
    outDir += '_v' + str(ver)
    print(outDir)
    fig, ax = plt.subplots()
    config.plot(ax, showGrid=False)
    config.writeInfo(outDir)
    print("Configuration loaded")
    routeDir = os.path.join(outDir, "routes/")

    sat = SAT(config)
    # # SOLVE THE PROBLEM
    print("Solving Problem")
    sat.solve()
    agents = sat.readSolution()
    print("agents trajectories")
    for agent in agents:
        agent.plot(ax)
        agent.writeTrajTxt(routeDir)

    outfile = os.path.join(outDir, 'path.png')
    plt.savefig(outfile)
    plt.show()
    return 0


if __name__ == '__main__':
    outDir = "tests/croz"
    main(outDir)
