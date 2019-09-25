#!bin/bash/python3
# import warnings as warn
import os
import csv
# import sys
# import time
# math
# import numpy as np
# plot
import matplotlib.pyplot as plt
# lib
from lib.utils import *
from lib.config import Config
from lib.shape import ShapeConfig
# gis
from osgeo import ogr
import utm
from shapely.geometry import Point, Polygon
from shapely.wkb import loads


class RookConfig(ShapeConfig):
    def __init__(self, file, step=100):
        # reads file and returns a x and y cord list as well as polygon object
        # break up zones
        zoneCords = [[(80200, 1473000), (80700, 1473000), (80700, 1470500), (78200, 1470500)],]
        self.zoneIdx = 0
        self.zonePolys = [Polygon(z) for z in zoneCords]

        # overlay key points
        self.keyPoints = {'erook': (-77.4632,   169.27899)}

        super(RookConfig, self).__init__(file, step)

    def setAgentParameters(self):
        # base point
        baseIdx = self.stateSpace[0]
        self.base = ind2sub(baseIdx, self.worldSize)
        # agent init
        self.maxTime = 50
        # agent index is in subrange NOT global statespace
        self.initAgent = [2, 8]
        self.nAgent = len(self.initAgent)

    def parseFile(self, file, longLat=False):
        super(RookConfig, self).parseFile(file)
        self.theta = 15 * np.pi / 180
        self.R = rot2D(self.theta)
        self.flatCords = np.dot(self.R, self.flatCords.T).T

    def polyPrune(self):
        # prune for containment
        if self.zoneIdx == -1:
            # ignore the zone splits
            polys = [self.poly]
        else:
            polys = [self.poly, self.zonePolys[self.zoneIdx]]

        self.stateSpace = [s for s in range(self.nStates) if self.inPoly(
                                          polys, self.world[:, s])]

    def plotZones(self, ax):
        colors = ['b', 'r', 'g', 'm', 'c', 'y']
        for zone, color in zip(self.zonePolys, colors):
            x = [point[0] for point in zone.exterior.coords]
            y = [point[1] for point in zone.exterior.coords]
            ax.plot(x, y, color=color)

    def plotKeyPonts(self, ax):
        for key, val in self.keyPoints.items():
            print(val)
            easting, northing, _ , _  = utm.from_latlon(val[0], val[1])
            UTMCords = np.array([easting, northing])
            # ROTATE THE DAMN CORDS
            UTMCordsRot = np.dot(self.R, UTMCords.T)
            print(UTMCordsRot)
            ax.scatter(*UTMCordsRot[0:2], color='k')
            ax.annotate(key, xy=UTMCordsRot[0:2], xycoords='data')

    def UTM2LatLong(self, utmCord):
        # overwrite utm to gps to reverse the rotation
        utmAligned = np.dot(self.R.T, np.array(utmCord))
        return utm.to_latlon(utmAligned[0], utmAligned[1], *self.UTMZone)

    def plot(self, ax, showGrid=True):
        super(RookConfig, self).plot(ax, showGrid=showGrid)
        # self.plotZones(ax)
        self.plotKeyPonts(ax)


if __name__ == '__main__':
    dataDir = "../data/croz_east"
    cordsFile = "croz_rook.csv"
    file = os.path.join(dataDir, cordsFile)
    config = RookConfig(file, step=30)

    # plot
    fig, ax = plt.subplots()
    config.plot(ax)
    plt.show()
    print(config.costmap)
