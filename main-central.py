#!bin/bash/python3
import warnings as warn
import os
import sys
import time
# math
import numpy as np
import numpy.linalg as la
import numpy.random as rand
import cvxpy as cvx
from gurobipy import *
# plot
import matplotlib.pyplot as plt
# lib
from lib.agent import Agent
from lib.config import Config
from lib.shape import ShapeConfig
from lib.crozConfig import CrozConfig
from lib.rookConfig import RookConfig
from lib.roydsConfig import RoydsConfig
# from lib.utils import *


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
               MIPGap=5e-2,
               MIPGapAbs=5e-2)
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
    #agent parameters
    agentParameters={}

    agentParameters["base"] = 9
    agentParameters["maxTime"] = 40
    agentParameters["initPos"] = [9]

    #gen parameters
    step = 20

    # input files
    # croz west
    # dateDir = "data/croz_geofence"
    # cordsFile = "outer.csv"
    # file = os.path.join(dateDir, cordsFile)
    # config = CrozConfig(file, step=40)
    # crox east
    dataDir = "data/croz_east"
    cordsFile = "croz_rook.csv"

    dataDir = "data/royds"
    cordsFile = "royds_geofence_latlon.csv"
    file = os.path.join(dataDir, cordsFile)
    config = RoydsConfig(file, agentParameters, step=step)


    config.writeInfo(outDir)
    print("Configuration loaded")
    routeDir = os.path.join(outDir, "routes/")

    # SOLVE THE PROBLEM
    print("\nSolving Problem\n")
    agents = solve_oneshot(config)
    fig, ax = plt.subplots()
    print("agents trajectories")
    for agent in agents:
        # print(agent.trajectory)
        agent.plot(ax)
        agent.writeTrajTxt(routeDir)

    outfile = os.path.join(outDir, 'path.png')
    config.plot(ax, showGrid = False)
    plt.savefig(outfile)
    plt.show()
    return 0


if __name__ == '__main__':
    outDir = "tests/royds_20_n1"
    main(outDir)
