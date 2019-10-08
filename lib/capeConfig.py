#!bin/bash/python3
# import warnings as warn
import os
import csv
# import sys
# import time
# math
import numpy as np
# plot
import matplotlib.pyplot as plt
# lib
try:
    from .config import Config
    from .shape import ShapeConfig
    from .utils import *
except (SystemError, ImportError):
    from config import Config
    from shape import ShapeConfig
    from utils import *
# gis
import utm
from shapely.geometry import Point, Polygon
from shapely.wkb import loads


class CrozConfig(ShapeConfig):
    def __init__(self, agentParameters, step, zone=-1, prefix=False):
        # reads file and returns a x and y cord list as well as polygon object
        # break up zones 
        zoneCords = [[(78200, 1473000), (78700, 1473000), (78700, 1472550), (78200, 1472550)],
                     [(78700, 1472800), (79000, 1472800),
                      (79000, 1472200), (78700, 1472200)],
                     [(79000, 1472500), (79500, 1472500),
                      (79500, 1471800), (79000, 1471800)],
                     [(78200, 1472550), (78700, 1472550),
                      (78700, 1472000), (78200, 1472000)],
                     [(78700, 1472200), (79000, 1472200), (79000, 1471500), (78700, 1471500)]]
        self.zoneIdx = zone
        self.zonePolys = [Polygon(z) for z in zoneCords]

        # overlay key points
        self.keyPoints = {'p':     (-77.455917, 169.21753),
                          'c':     (-77.454753, 169.216886),
                          'bn':    (-77.44906,  169.22322),
                          'mle':   (-77.45362,  169.23247),
                          'fg':    (-77.459294, 169.245182)}
        if prefix:
            dataDir = "data/croz_geofence"
        else:
            dataDir = "../data/croz_geofence"
        cordsFile = "croz_west.csv"
        file = os.path.join(dataDir, cordsFile)

        super(CrozConfig, self).__init__(file, agentParameters, step)

    def parseFile(self, file, longLat=False):
        super(CrozConfig, self).parseFile(file)
        self.theta = 15 * np.pi / 180
        self.R = rot2D(self.theta)
        self.flatCords = np.dot(self.R, self.flatCords.T).T

    def UTM2LatLong(self, utmCord):
        # overwrite utm to gps to reverse the rotation
        utmAligned = np.dot(self.R.T, np.array(utmCord))
        return super(RookConfig, self).UTM2LatLong(utmAligned)


class RookConfig(ShapeConfig):
    def __init__(self, agentParameters, step):
        # reads file and returns a x and y cord list as well as polygon object
        # break up zones
        zoneCords = [[(80000, 1472200), (80550, 1472200), (80550, 1472050), (80000, 1471850)],
                     [(80000, 1471850), (80550, 1472050), (80550, 1471700), (80000, 1471700)],]
        self.zoneIdx = -1
        self.zonePolys = [Polygon(z) for z in zoneCords]

        # overlay key points
        self.keyPoints = {'erook': (-77.4632,   169.27899)}

        dataDir = "../data/croz_east"
        cordsFile = "croz_rook.csv"
        file = os.path.join(dataDir, cordsFile)
        super(RookConfig, self).__init__(file, agentParameters, step=step)

    def parseFile(self, file, longLat=False):
        super(RookConfig, self).parseFile(file)
        self.theta = 15 * np.pi / 180
        self.R = rot2D(self.theta)
        self.flatCords = np.dot(self.R, self.flatCords.T).T

    def UTM2LatLong(self, utmCord):
        # overwrite utm to gps to reverse the rotation
        utmAligned = np.dot(self.R.T, np.array(utmCord))
        return super(RookConfig, self).UTM2LatLong(utmAligned)


class RoydsConfig(ShapeConfig):
    def __init__(self, agentParameters, step=100):
        # reads file and returns a x and y cord list as well as polygon object
        # break up zones
        self.zoneIdx = -1

        # zoneCords = [[(80000, 1472200), (80550, 1472200), (80550, 1472050), (80000, 1471850)],
        #              [(80000, 1471850), (80550, 1472050), (80550, 1471700), (80000, 1471700)],]
        # self.zonePolys = [Polygon(z) for z in zoneCords]

        # overlay key points
        self.keyPoints = {}

        dataDir = "../data/royds"
        cordsFile = "royds_geofence_latlon.csv"
        file = os.path.join(dataDir, cordsFile)
        super(RoydsConfig, self).__init__(file, agentParameters, step)


if __name__ == '__main__':
    step = 40
    agentParameters = {}
    agentParameters["base"] = -1
    agentParameters["maxTime"] = 55
    agentParameters["initPos"] = [-1, -12]

    config = CrozConfig(agentParameters=agentParameters,
                        step=step, zone=3)
    # config = RookConfig(agentParameters=None, step=25)
    # config = RoydsConfig(agentParameters=None, step=20)
    # plot
    fig, ax = plt.subplots()
    config.plot(ax)
    plt.show()
