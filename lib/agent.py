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

        self.keyPoints = {"hut": [-77.4610948, 169.1860094]}
        self.transferSpeed = 12.0

    def __repr__(self):
        pass
        # print the trajectory
        # outsrt = f""
        # for pt in self.pts:
        #     outsrt += f"[{pt[0]}, {pt[1]}]\n"
        # return outsrt

    def append(self, pt):
        # append to the traj history
        self.pts.append(np.array(pt))

    def writeTxt(self, filename, mapFunc, alt, spd):
        # writes the trajectory as a txt file
        # Lat,Long,Alt,Speed,Picture,ElevationMap,WP,CameraTilt,UavYaw,DistanceFrom
        with open(filename, "w+") as f:
            for i, pt in enumerate(self.pts):
                lat, lng = mapFunc(pt)
                if i == 0:
                    f.write("%s,%s,%s,%s,FALSE,,1,90\n" % (lat, lng, alt, spd))
                elif i == len(self.pts)-1:
                    f.write("%s,%s,%s,%s,FALSE,,1,0\n" % (lat, lng, alt, spd))
                else:
                    f.write("%s,%s,%s,%s,FALSE,,1\n" % (lat, lng, alt, spd))

    def plot(self, ax, colorize=False):
        # plots the trajectory
        plotPlot = np.array(self.pts)
        if len(plotPlot.shape) > 1:
            # start
            ax.scatter(*self.pts[0], marker="*", color=self.color)
            # end
            # ax.scatter(*self.pts[-1], marker="^", color=self.color)
            # path
            trajLen = plotPlot.shape[0]
            cm = plt.cm.get_cmap('plasma', trajLen)
            for i in range(plotPlot.shape[0]-1):
                color = cm(i % trajLen) if colorize else self.color
                ax.plot(plotPlot[i:i+2, 0],
                        plotPlot[i:i+2, 1],
                        color=color)


class Agent(object):
    def __init__(self, ID, config, color='b'):
        self.id = ID
        self.config = config
        self.color = color
        self.alt = 50  # altitude in m of the quad
        self.speed = 4.0  # speed in m/s
        # init trajectory
        self.trajectory = Trajectory(color=self.color)

    def makeTrajectory(self, statePath):
        # takes the state path and return the tranformed path in UMT
        config = self.config
        # get start point
        path = [config.stateSpace[statePath[0]]]
        # makes trajectory
        for state in statePath[1:]:
            # convert to world index
            worldIdx = config.stateSpace[state]
            # convert to world point
            pt = config.world[:, worldIdx]
            if worldIdx != path[-1]:  # remove no motion
                path.append(worldIdx)
                self.trajectory.append(pt)
        pathLen = len(path)*config.step
        print("Path Length (km): {:2.4f}. Flight Time (min): {:2.4f}".format(
               pathLen, pathLen/self.speed/60))

    def writeTrajTxt(self, outpath):
        if not os.path.exists(outpath):
            os.makedirs(outpath)
        # write the trajectory
        filename = outpath + str(self.id) + ".csv"
        self.trajectory.writeTxt(filename, self.config.UTM2LatLong,
                                 self.alt, self.speed)

    def plot(self, ax):
        self.trajectory.plot(ax, colorize=False)


if __name__ == '__main__':
    pass
