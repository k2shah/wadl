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

        self.keyPoints = {"hut": [-77.4610948, 169.1860094],
                          "hut-tz": [-77.461540, 169.18600],
                          "hut-lz": [-77.4614790, 169.1849841]}
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
            # take off
            # add hut-lz as takeoff point
            lat, lng = self.keyPoints['hut-tz']
            f.write("%s,%s,%s,%s,FALSE,,1\n" % (lat, lng, 70, self.transferSpeed))
            # routes
            for i, pt in enumerate(self.pts):
                lat, lng = mapFunc(pt)
                offset = .05 - .1 * (i % 2)  # to force speed chg each point
                f.write("%s,%s,%s,%s,FALSE,,1\n" % (lat, lng, alt, spd+offset))
            # end route
            # get higher above last point
            pt = self.pts[-1]
            lat, lng = mapFunc(pt)
            f.write("%s,%s,%s,%s,FALSE,,1\n" % (lat, lng, 70, self.transferSpeed))
            # fly to lz
            lat, lng = self.keyPoints['hut-lz']
            f.write("%s,%s,%s,%s,FALSE,,1\n" % (lat, lng, 50, 5))
            # move to land alt
            f.write("%s,%s,%s,%s,FALSE,,1\n" % (lat, lng, 20, 3))

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
        # print("Path Length (km): {:2.4f}. Flight Time (min): {:2.4f}".format(
        #        pathLen, pathLen/self.speed/60))

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
