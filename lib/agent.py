#!bin/bash/python
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
try:
    from .utils import *
except (SystemError, ImportError):
    from utils import *


class Trajectory(object):

    def __init__(self, color='k'):
        # makes the trajectory object
        # pt is the initial point of the trajectory
        self.pts = []
        self.color = color

    def __repr__(self):
        # print the trajectory
        outsrt = f""
        for pt in self.pts:
            outsrt += f"[{pt[0]}, {pt[1]}]\n"
        return outsrt

    def append(self, pt):
        # append to the traj history
        self.pts.append(np.array(pt))

    def writeTxt(self, filename, mapFunc, alt):
        # writes the trajectory as a txt file
        # Lat,Long,Alt,Speed,Picture,ElevationMap,WP,CameraTilt,UavYaw,DistanceFrom
        with open(filename, "w+") as f:
            for pt in self.pts:
                lat, long = mapFunc(pt)
                f.write(f"{lat},{long},{alt},,FALSE,,1\n")

    def plot(self, ax, colorize=False):
        # plots the trajectory
        plotPlot = np.array(self.pts)
        if len(plotPlot.shape) > 1:
            # start
            ax.scatter(*self.pts[0],
                       marker="o", color=self.color)
            # end
            ax.scatter(*self.pts[-1],
                       marker="^", color=self.color)
            # path
            trajLen = plotPlot.shape[0]
            cm = plt.cm.get_cmap('plasma', trajLen)
            for i in range(plotPlot.shape[0]-1):
                color = cm(i % trajLen) if colorize else self.color
                ax.plot(plotPlot[i:i+2, 0],
                        plotPlot[i:i+2, 1],
                        color=color)


class Agent(object):
    def __init__(self, id, config, color='b'):
        self.id = id
        self.config = config
        self.color = color
        self.alt = 30  # altitude in m of the quad
        self.speed = 3.0  # speed in m/s
        # self.cvxVar = cvx.Variable((config.S, config.maxTime), boolean=True)
        # init trajectory
        self.trajectory = Trajectory(color=self.color)

    def makeTrajectory(self):
        config = self.config
        x = self.cleanSolution()
        # print(x)
        # get start point
        stateIdx = np.argmax(x[:, 0])
        path = [config.stateSpace[stateIdx]]
        # makes trajectory
        for t in range(1, x.shape[1]):
            stateIdx = np.argmax(x[:, t])
            worldIdx = config.stateSpace[stateIdx]
            # print(worldIdx)
            pt = config.world[:, worldIdx]
            if worldIdx != path[-1]:
                path.append(worldIdx)
                self.trajectory.append(pt)
        print(f"{len(path)}: ", path)
        pathLen= len(path)*config.step
        print(f"path len: {pathLen}. Flight time: {pathLen/self.speed}")

    def cleanSolution(self):
        # this removes blocks of no motion
        x = []
        lastWasZero = False
        for t in range(0, self.config.maxTime):
            if self.cvxVar.value[0, t] == 1:
                if lastWasZero:
                    # drop if adjacent zeros
                    continue
                else:
                    x.append(self.cvxVar.value[:, t])
                    lastWasZero = True
            else:
                x.append(self.cvxVar.value[:, t])
                lastWasZero = False
        return np.array(x).T

    def writeTrajTxt(self, outpath):
        if not os.path.exists(outpath): os.makedirs(outpath)
        # write the trajectory
        filename = outpath + str(self.id) + ".csv"
        self.trajectory.writeTxt(filename, self.config.UTM2LatLong, self.alt)

    def stage(self, obj, cnts):
        # unpack
        id = self.id
        config = self.config

        # make variable
        nStates = len(config.stateSpace)
        self.cvxVar = cvx.Variable((nStates, config.maxTime), boolean=True)
        X = self.cvxVar

        # boundary constraints
        # index of State space
        s = config.initAgent[id]

        # cnts += [X <= 1]
        cnts += [X[s, 0] == 1]  # initial location
        cnts += [cvx.sum(X[:, 0]) == 1]  # one spot
        cnts += [X[s, -1] == 1]  # final location

        # running constraints
        for t in range(1, config.maxTime):
            cnts += [cvx.sum(X[:, t]) == 1]  # one spot
            cnts += [X[:, t] <= config.Ts * X[:, t - 1]]  # motion

        # # coverage constraints
        # for s in range(nStates):
        #     cnts += [cvx.sum(X[s, :]) >= 1]  # all spots at least once

        # range constraints
        # for t in range(config.maxTime):
        #     cnts +=[config.costmap.T* X[:, t] <= max(90-t, 10)]

        # objective
        for t in range(1, config.maxTime):
            obj += [config.costmap.T * X[:, t]]

    def plot(self, ax):
        self.trajectory.plot(ax, colorize=False)


if __name__ == '__main__':
    pass
