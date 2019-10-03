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


class CrozConfig(ShapeConfig):
    def __init__(self, file, agentParameters, step, zone=-1):
        # reads file and returns a x and y cord list as well as polygon object
        # break up zones
        zoneCords = [[(78200, 1473000), (78700, 1473000), (78700, 1472550), (78200, 1472550)],
                     [(78700, 1472800), (79000, 1472800), (79000, 1472200), (78700, 1472200)],
                     [(79000, 1472500), (79500, 1472500), (79500, 1471800), (79000, 1471800)],
                     [(78200, 1472550), (78700, 1472550), (78700, 1472000), (78200, 1472000)],
                     [(78700, 1472200), (79000, 1472200), (79000, 1471500), (78700, 1471500)]]
        self.zoneIdx = zone
        self.zonePolys = [Polygon(z) for z in zoneCords]

        # overlay key points
        self.keyPoints = {'p':     (-77.455917, 169.21753),
                          'c':     (-77.454753, 169.216886),
                          'bn':    (-77.44906,  169.22322),
                          'mle':   (-77.45362,  169.23247),
                          'fg':    (-77.459294, 169.245182)}
                          # 'erook': (-77.4632,   169.27899)}

        super(CrozConfig, self).__init__(file, agentParameters, step)

    def parseFile(self, file, longLat=False):
        super(CrozConfig, self).parseFile(file)
        self.theta = 15 * np.pi / 180
        self.R = rot2D(self.theta)
        self.flatCords = np.dot(self.R, self.flatCords.T).T

    def polyPrune(self):
        # prune for containment
        self.stateSpace = [s for s in range(self.nStates) if self.inPoly(
                                          [self.poly, self.zonePolys[self.zoneIdx]],
                                          self.world[:, s])]

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
        super(CrozConfig, self).plot(ax, showGrid=showGrid)
        self.plotZones(ax)
        self.plotKeyPonts(ax)


if __name__ == '__main__':
    dataDir = "../data/croz_geofence"
    cordsFile = "croz_west.csv"
    file = os.path.join(dataDir, cordsFile)
    config = CrozConfig(file, agentParameters=None, step=40, zone=1)

    # plot
    fig, ax = plt.subplots()
    config.plot(ax)
    plt.show()
    print(config.costmap)
