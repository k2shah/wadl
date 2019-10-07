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


class RoydsConfig(ShapeConfig):
    def __init__(self, agentParameters, step=100):
        # reads file and returns a x and y cord list as well as polygon object
        # break up zones
        zoneCords = [[(80000, 1472200), (80550, 1472200), (80550, 1472050), (80000, 1471850)],
                     [(80000, 1471850), (80550, 1472050), (80550, 1471700), (80000, 1471700)],]
        self.zoneIdx = -1
        self.zonePolys = [Polygon(z) for z in zoneCords]

        # overlay key points
        self.keyPoints = {}

        dataDir = "../data/royds"
        cordsFile = "royds_geofence_latlon.csv"
        file = os.path.join(dataDir, cordsFile)
        super(RoydsConfig, self).__init__(file, agentParameters, step)

if __name__ == '__main__':
    config = RoydsConfig(agentParameters=None, step=20)

    # plot
    fig, ax = plt.subplots()
    config.plot(ax)
    plt.show()
    #print(config.costmap)
