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
from lib.utils import *


class Trajectory(object):

    def __init__(self, pt, color='k'):
        # makes the trajectory object
        # pt is the initial point of the trajectory
        self.pts = np.array(pt)
        self.color = color

    def __repr__(self):
        # print the trajectory
        outsrt = f""
        for i in range(self.pts.shape[0]):
            outsrt += f"[{self.pts[i,0]}, {self.pts[i,1]}], {i}, {la.norm(self.pts[i,:], 1)}\n"

        return outsrt

    def append(self, pt):
        # append to the traj history
        self.pts = np.vstack((self.pts, np.array(pt)))

    def plot(self, ax, colorize=False):
        # plots the trajectory
        if len(self.pts.shape) > 1:
            # start
            ax.scatter(*self.pts[0, :],
                       marker="o", color=self.color)
            # path
            trajLen = self.pts.shape[0]
            cm = plt.cm.get_cmap('plasma', trajLen )
            for i in range(self.pts.shape[0]-1):
                color = cm(i % trajLen) if colorize else self.color
                ax.plot(self.pts[i:i+2, 0],
                        self.pts[i:i+2, 1],
                        color=color)


class Agent(object):
    def __init__(self, id, config, color='b'):
        self.id = id
        self.config = config
        self.color = color
        self.cvxVar = cvx.Variable((config.S, config.maxTime), boolean=True)
        # init trajectory
        self.trajectory = Trajectory(config.initAgent[id], color=self.color)

    def makeTrajectory(self):
        config = self.config
        x = self.cleanSolution()
        # makes trajectory
        for t in range(1, x.shape[1]):
            cord = ind2sub(np.argmax(x[:, t]), config.worldSize)
            self.trajectory.append(cord)

    def cleanSolution(self):
        # this removes blocks of no motion
        x = []
        lastWasZero = False
        for t in range(self.config.maxTime):
            if self.cvxVar.value[0, t] == 1:
                if lastWasZero == True:
                    # drop if adjacent zeros
                    continue
                else:
                    x.append(self.cvxVar.value[:, t])
                    lastWasZero = True
            else:
                x.append(self.cvxVar.value[:, t])
                lastWasZero = False
        return np.array(x).T

    def stage(self, obj, cnts):
        # unpack
        id = self.id
        config = self.config

        # make variable
        self.cvxVar = cvx.Variable((config.S, config.maxTime), boolean=True)
        X = self.cvxVar

        # boundary constraints
        s = sub2ind(config.initAgent[id], config.worldSize)
        # cnts += [X <= 1]
        cnts += [X[s, 0] == 1]  # initial location
        cnts += [cvx.sum(X[:, 0]) == 1]  # one spot
        cnts += [X[s, -1] == 1]  # final location

        # running constraints
        for t in range(1, config.maxTime):
            cnts += [cvx.sum(X[:, t]) == 1]  # one spot
            cnts += [X[:, t] <= config.Ts * X[:, t - 1]]  # motion

        # coverage constraints
        for s in range(config.S):
            cnts += [cvx.sum(X[s, :]) >= 1]  # all spots at least once

        # range constraints
        for t in range(config.maxTime):
            cnts +=[config.costmap.T* X[:, t] <= max(90-t, 10)]


        # objective
        for t in range(1, config.maxTime):
            obj += [config.costmap.T* X[:, t]]

    def plot(self, ax):
        self.trajectory.plot(ax, colorize=True)


if __name__ == '__main__':
    pass
