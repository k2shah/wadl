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

    #add multi agent
    nStates = len(config.stateSpace)
    # coverage constraints
    # all spots at least once
    for s in range(nStates):
        cnts += [cvx.sum([cvx.sum(agent.cvxVar[s, :]) for agent in agents]) >= 1]


    prob = cvx.Problem(cvx.Minimize(cvx.sum(obj)), cnts)
    prob.solve(solver=cvx.GUROBI,
               verbose=True,
               MIPGap=1e-1,
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
    #input files
    dateDir = "data/croz_geofence"
    shapeFile = "croz_outer_bound.shp"
    file = os.path.join(dateDir, shapeFile)
    config = ShapeConfig(file, step=80)
    #config = Config("small")


    config.writeInfo(outDir)
    routeDir = os.path.join(outDir, "routes/")

    # SOLVE THE PROBLEM
    agents = solve_oneshot(config)



    fig, ax = plt.subplots()
    print("agents trajectories")
    for agent in agents:
        print(agent.trajectory)
        agent.plot(ax)
        agent.writeTrajTxt(routeDir)

    outfile = os.path.join(outDir, 'path.png')
    config.plotPolygon(ax)
    plt.savefig(outfile)
    plt.show()

    return 0

if __name__ == '__main__':
    outDir = "tests/test4"
    main(outDir)
