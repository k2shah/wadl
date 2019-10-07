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
from utils import *
from config import Config
from shape import ShapeConfig
# gis
from osgeo import ogr
import utm
from shapely.geometry import Point, Polygon
from shapely.wkb import loads


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

if __name__ == '__main__':
    config = RookConfig(agentParameters=None, step=25)

    # plot
    fig, ax = plt.subplots()
    config.plot(ax)
    plt.show()
    print(config.costmap)
