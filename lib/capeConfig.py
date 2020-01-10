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
    from .metagraph import Metagraph
except (SystemError, ImportError):
    from config import Config
    from shape import ShapeConfig
    from utils import *
    from metagraph import Metagraph
# gis
import utm
from shapely.geometry import Point, Polygon
from shapely.wkb import loads


class CrozConfig(ShapeConfig):
    def __init__(self, agentParameters, step, zone=-1, prefix=False):
        # reads file and returns a x and y cord list as well as polygon object
        # break up zones
        zoneCords = []

        # croz 40

        zoneCords.append([(78030, 1473100), (78635, 1472920),
                         (78635, 1472550), (78200, 1472550)])
        zoneCords.append([(78635, 1472780), (79100, 1472500),
                         (79100, 1472250), (78635, 1472250)])
        zoneCords.append([(79100, 1472500), (79500, 1472300),
                         (79500, 1471840), (79100, 1471900)])
        zoneCords.append([(78200, 1472550), (78635, 1472550),
                         (78635, 1471900), (78210, 1472100)])
        zoneCords.append([(78635, 1472250), (79100, 1472250),
                          (79100, 1471900), (78635, 1471900)])
        zoneCords.append([(78635, 1471900), (79000, 1471900),
                          (79000, 1471450), (78700, 1471450)])




        # croz 30 (fine)

        # zoneCords.append([(78040, 1473100), (78540, 1472950),
        #                   (78540, 1472700), (78200, 1472700)])

        # zoneCords.append([(78540, 1472950), (79100, 1472500),
        #                   (79100, 1472450), (78540, 1472450)])

        # zoneCords.append([(79100, 1472450), (79500, 1472300),
        #                   (79500, 1471840), (79100, 1471900)])

        # zoneCords.append([(78200, 1472700), (78540, 1472700),
        #                   (78540, 1472450), (78200, 1472450)])

        # zoneCords.append([(78200, 1472450), (78900, 1472450),
        #                   (78900, 1472250), (78200, 1472250)])

        # zoneCords.append([(78200, 1472250), (78900, 1472250),
        #                   (78900, 1471900), (78200, 1471900)])

        # zoneCords.append([(78900, 1472450), (79100, 1472450),
        #                   (79100, 1471900), (78900, 1471900)])

        # zoneCords.append([(78650, 1471900), (79000, 1471900),
        #                   (79000, 1471450), (78700, 1471450)])

        self.zoneIdx = zone
        self.zonePolys = [Polygon(z) for z in zoneCords]

        # overlay key points
        self.keyPoints = {'p':     (-77.455917, 169.21753),
                          'c':     (-77.454753, 169.216886),
                          'bn':    (-77.44906,  169.22322),
                          'mle':   (-77.45362,  169.23247),
                          'fg':    (-77.459294, 169.245182)}

        dataDir = "data/croz_geofence"
        cordsFile = "croz_west_3.csv"
        file = os.path.join(dataDir, cordsFile)
        super(CrozConfig, self).__init__(file, agentParameters,
                                         step=step, prefix=prefix)

    def parseFile(self, file, longLat=False):
        super(CrozConfig, self).parseFile(file, longLat=True)
        self.theta = 15 * np.pi / 180
        self.R = rot2D(self.theta)
        self.flatCords = np.dot(self.R, self.flatCords.T).T

    def UTM2LatLong(self, utmCord):
        # overwrite utm to gps to reverse the rotation
        utmAligned = np.dot(self.R.T, np.array(utmCord))
        return super(CrozConfig, self).UTM2LatLong(utmAligned)


class RookConfig(ShapeConfig):
    def __init__(self, agentParameters, step, prefix=False):

        # reads file and returns a x and y cord list as well as polygon object
        # break up zones
        zoneCords = [[(80000, 1472200), (80550, 1472200),
                      (80550, 1472050), (80000, 1471850)],
                     [(80000, 1471850), (80550, 1472050),
                      (80550, 1471700), (80000, 1471700)]]
        self.zoneIdx = -1
        self.zonePolys = [Polygon(z) for z in zoneCords]

        # overlay key points
        self.keyPoints = {'erook': (-77.4632,   169.27899)}

        dataDir = "data/croz_east"
        cordsFile = "croz_rook_3.csv"
        file = os.path.join(dataDir, cordsFile)
        super(RookConfig, self).__init__(file, agentParameters,
                                         step=step, prefix=prefix)

    def parseFile(self, file, longLat=False):
        super(RookConfig, self).parseFile(file, longLat=True)
        self.theta = 15 * np.pi / 180
        self.R = rot2D(self.theta)
        self.flatCords = np.dot(self.R, self.flatCords.T).T

    def UTM2LatLong(self, utmCord):
        # overwrite utm to gps to reverse the rotation
        utmAligned = np.dot(self.R.T, np.array(utmCord))
        return super(RookConfig, self).UTM2LatLong(utmAligned)


class RoydsConfig(ShapeConfig):
    def __init__(self, agentParameters, step, prefix=False):
        # reads file and returns a x and y cord list as well as polygon object
        # break up zones
        self.zoneIdx = -1
        # self.zonePolys = [Polygon(z) for z in zoneCords]

        # overlay key points
        self.keyPoints = {}

        dataDir = "data/royds"
        cordsFile = "royds_geofence_latlon.csv"
        file = os.path.join(dataDir, cordsFile)
        super(RoydsConfig, self).__init__(file, agentParameters,
                                          step=step, prefix=prefix)


if __name__ == '__main__':
    step = 40
    agentParameters = {}
    agentParameters["base"] = 7
    agentParameters["maxTime"] = 35
    agentParameters["initPos"] = [0, 9]

    config = CrozConfig(agentParameters=agentParameters, step=step, zone=0)
    # config = RookConfig(agentParameters=agentParameters, step=step)
    # config = RoydsConfig(agentParameters=agentParameters, step=step
    # metagraph = Metagraph(config.stateSpace,
    #                       config.con,
    #                       config.worldSize)
    # metagraph.reduce(3, verbose=True)
    # print(metagraph)
    # plot
    fig, ax = plt.subplots()
    config.plot(ax, showCamera=False)
    # fig.savefig("0000.png")
    # metagraph.plot(ax, config.world)
    plt.show()
