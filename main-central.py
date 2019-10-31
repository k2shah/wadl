#!/usr/bin/python3
import warnings as warn
import os
import sys
import time
# math
import numpy as np
import numpy.linalg as la
import numpy.random as rand
import cvxpy as cvx
# plot
import matplotlib.pyplot as plt
# lib
from lib.agent import Agent
from lib.capeConfig import CrozConfig, RookConfig, RoydsConfig
from lib.utils import *
from gurobipy import *


class MILP(object):
    """docstring for MILP"""
    def __init__(self, config):
        # make objects
        self.config = config
        # init optimization problem data
        self.obj = []
        self.cnts = []
        self.nStates = len(self.config.stateSpace)

        self.makeVars()
        self.setConts()

    def makeVars(self):
        self.cvxVars = [cvx.Variable((self.nStates, self.config.maxTime), boolean=True)
                        for i in range(self.config.nAgent)]

    def setConts(self):
        for i, X in enumerate(self.cvxVars):
            # boundary constraints
            s = self.config.initAgent[i]
            # index of State space
            self.cnts += [X[s, 0] == 1]  # initial location
            self.cnts += [cvx.sum(X[:, 0]) == 1]  # one spot
            self.cnts += [X[s, -1] == 1]  # final location

            # running constraints
            for t in range(1, self.config.maxTime):
                self.cnts += [cvx.sum(X[:, t]) == 1]  # one spot
                self.cnts += [X[:, t] <= self.config.Ts * X[:, t - 1]]  # motion

        # range constraints
        # for t in range(config.maxTime):
        #     cnts +=[config.costmap.T* X[:, t] <= max(90-t, 10)]

            # objective
            for t in range(1, self.config.maxTime):
                self.obj += [self.config.costmap.T * X[:, t]]

        # coverage constraints
        # all spots at least once
        for s in range(self.nStates):
            self.cnts += [cvx.sum([cvx.sum(self.cvxVars[i][s, :])
                          for i in range(self.config.nAgent)]) >= 1]

    def solve(self):
        self.prob = cvx.Problem(cvx.Minimize(cvx.sum(self.obj)), self.cnts)
        self.prob.solve(solver=cvx.GUROBI,
                        verbose=True,
                        MIPGap=5e-2,
                        MIPGapAbs=5e-2)
        if self.prob.status == "optimal":
            print("Solution Found")
        else:
            print(self.prob.status)
            raise RuntimeError("solution not found")

    def readSolution(self):
        colors = ['b', 'g', 'r', 'm']
        agents = [Agent(ID, self.config, color=color)
                  for ID, color in zip(range(self.config.nAgent), colors)]

        # parse solutions
        for i, agent in enumerate(agents):
            # this removes blocks of no motion
            x = []
            lastWasZero = False
            for t in range(0, self.config.maxTime):
                if self.cvxVars[i].value[0, t] == 1:
                    if lastWasZero:
                        # drop if adjacent zeros
                        continue
                    else:
                        x.append(self.cvxVars[i].value[:, t])
                        lastWasZero = True
                else:
                    x.append(self.cvxVars[i].value[:, t])
                    lastWasZero = False
            x = np.array(x).T
            # process path
            # path of states
            path = ([np.argmax(x[:, t]) for t in range(0, x.shape[1])])
            agent.makeTrajectory(path)

        return agents


def main(outDir):
    # agent parameters
    agentParameters = {}


    # zone 0
    agentParameters["base"] = 1
    agentParameters["maxTime"] = 40
    agentParameters["initPos"] = [0, 2]
    nAgent = len(agentParameters["initPos"])

    # gen parameters
    step = 60
    zone = 3
    ver = 1
    # input files
    # croz west
    config = CrozConfig(agentParameters, step=step, zone=zone,
                        prefix=True)
    # crox east
    # config = RoydsConfig(file, agentParameters, step=step)

    outDir += '_' + str(step) + '_n' + str(nAgent) + '_z' + str(zone)
    outDir += '_v' + str(ver)
    print(outDir)
    config.writeInfo(outDir)
    print("Configuration loaded")
    routeDir = os.path.join(outDir, "routes/")

    milp = MILP(config)
    # # SOLVE THE PROBLEM
    print("Solving Problem")
    milp.solve()
    agents = milp.readSolution()

    fig, ax = plt.subplots()
    print("agents trajectories")
    for agent in agents:
        # print(agent.trajectory)
        agent.plot(ax)
        agent.writeTrajTxt(routeDir)

    outfile = os.path.join(outDir, 'path.png')
    config.plot(ax, showGrid=False)
    plt.savefig(outfile)
    plt.show()
    return 0


if __name__ == '__main__':
    outDir = "tests/croz"
    main(outDir)
