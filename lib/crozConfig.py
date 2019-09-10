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
# gis
from osgeo import ogr
import utm
from shapely.geometry import Point, Polygon
from shapely.wkb import loads


class CrozConfig(Config):
    def __init__(self, step=100):
        # reads file and returns a x and y cord list as well as polygon object
        # import file
        dataDir = "data/croz_geofence"
        # shapeFile = "croz_outer_bound.shp"
        cordsFile = "outer.csv"
        file = os.path.join(dataDir, cordsFile)

        # read cords and convert to utm (long, lat)
        print(file)
        with open(file) as csvfile:
            data = [(line[1], line[2]) for line in csv.reader(csvfile, delimiter=',')]
            # toss 1st line and convert to float
            self.GPSData = [tuple(map(float, line)) for line in data[1:]]
        # convert to utm
        UTMData = ([utm.from_latlon(cords[1], cords[0]) for cords in self.GPSData])
        self.UTMZone = UTMData[0][2:]
        print(self.UTMZone)
        UTMCords = np.array([[data[0], data[1]] for data in UTMData])
        # rotate
        self.theta = 15 * np.pi/180
        self.R = rot2D(self.theta)
        UTMCordsRot = np.dot(self.R, UTMCords.T)

        # build polygon
        self.UTMCords = array2ListTuples(UTMCordsRot.T)
        print(self.UTMCords)
        self.poly = Polygon(self.UTMCords)

        zoneCords = [[(78200, 1473000), (78700, 1473000), (78700, 1472500), (78200, 1472500)],
                     [(78700, 1472800), (79000, 1472800), (79000, 1472200), (78700, 1472200)],
                     [(79000, 1472500), (79500, 1472500), (79500, 1471800), (79000, 1471800)],
                     [(78200, 1472500), (78700, 1472500), (78700, 1472000), (78200, 1472000)],
                     [(78700, 1472200), (79000, 1472200), (79000, 1471500), (78700, 1471500)]]
        self.zoneIdx = 4
        self.zonePolys = [Polygon(z) for z in zoneCords]

        # for i in range(len(splits)-1):
        #    self.polys.append(Polygon(self.UTMCords[splits[i]:splits[i+1]]))
        minx, miny, maxx, maxy = self.poly.bounds
        print(maxx-minx, maxy-miny)
        self.xGrid = np.linspace(minx, maxx, int((maxx - minx)/step))
        self.yGrid = np.linspace(miny, maxy, int((maxy - miny)/step))
        self.nX = len(self.xGrid)
        self.nY = len(self.yGrid)
        # world objects
        self.worldSize = (self.nX, self.nY)
        self.nStates = int(np.prod(self.worldSize))
        # world map index to point
        self.buildWorld()
        # launch point
        # remove points outside polygon
        self.buildTransition()
        self.polyPrune()

        baseIdx = self.stateSpace[0]
        self.base = ind2sub(baseIdx, self.worldSize)
        self.buildCostmap()
        # slice transition and costmap to only the valid states
        self.Ts = self.Ts[np.ix_(self.stateSpace, self.stateSpace)]
        # self.costmap = self.costmap[self.stateSpace]
        # agent init
        self.maxTime = 65
        self.initAgent = [126, 127, 128]
        self.nAgent = len(self.initAgent)

    def inPoly(self, poly, point):
        # checks if point (tuple) is in the polygon
        pt = Point(point)
        return poly.contains(pt)

    def polyPrune(self):
        # prune for containment
        inPolyStates = [s for s in range(self.nStates) if self.inPoly(self.poly, self.world[:, s])]
        self.stateSpace = [s for s in inPolyStates
                           if self.inPoly(self.zonePolys[self.zoneIdx], self.world[:, s])]
        print(self.stateSpace)
        print(len(self.stateSpace))

    def plotPolygon(self, ax):
        x = [point[0] for point in self.poly.exterior.coords]
        y = [point[1] for point in self.poly.exterior.coords]
        ax.plot(x, y, color = 'k')

    def plotZones(self, ax):
        colors = ['b', 'r', 'g', 'm', 'c', 'y']
        for zone, color in zip(self.zonePolys, colors):
            x = [point[0] for point in zone.exterior.coords]
            y = [point[1] for point in zone.exterior.coords]
            ax.plot(x, y, color = color)

    def UTM2LatLong(self, utmCord):
        utmAligned = np.dot(self.R.T, np.array(utmCord))
        return utm.to_latlon(utmAligned[0], utmAligned[1], *self.UTMZone)



    def plot(self, ax):
        super(CrozConfig, self).plot(ax)
        self.plotPolygon(ax)
        self.plotZones(ax)


if __name__ == '__main__':
    config = CrozConfig(step=40)

    # plot
    fig, ax = plt.subplots()
    config.plot(ax)
    plt.show()
    print(config.costmap)