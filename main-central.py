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


def solve_oneshot(config):
    # make objects
    colors = ['b', 'g', 'r', 'm']
    agents = [Agent(id, config, color=color) for id, color in zip(range(config.nAgent), colors)]

    # init optimization problem data
    obj = []
    cnts = []

    # fill problems
    for agent in agents:
        agent.stage(obj, cnts)
    # add multi agent
    nStates = len(config.stateSpace)
    # coverage constraints
    # all spots at least once
    for s in range(nStates):
        cnts += [cvx.sum([cvx.sum(agent.cvxVar[s, :]) for agent in agents]) >= 1]
    prob = cvx.Problem(cvx.Minimize(cvx.sum(obj)), cnts)
    prob.solve(solver=cvx.GUROBI,
               verbose=True,
               MIPGap=7e-2,
               MIPGapAbs=7e-2)
    # print("solving")
    # prob.solve(solver=cvx.ECOS_BB,
    #            verbose=True,
    #            mi_max_iters=10,
    #            mi_abs_eps=1e-3,
    #            mi_rel_eps=1e-2)
    print(prob.status)

    # parse solutions
    for agent in agents:
        agent.makeTrajectory()

    return agents


def main(outDir):
    # agent parameters
    agentParameters = {}

    agentParameters["base"] = 11
    agentParameters["maxTime"] = 45
    agentParameters["initPos"] = [5, 11, 20]
    nAgent = len(agentParameters["initPos"])

    # gen parameters
    step = 40
    zone = 2
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

    # SOLVE THE PROBLEM
    print("Solving Problem")
    agents = solve_oneshot(config)
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
