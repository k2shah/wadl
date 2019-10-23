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
    from .utils import *
except (SystemError, ImportError):
    from config import Config
    from utils import *
# gis
import utm
from shapely.geometry import Point, Polygon
from shapely.wkb import loads


class ShapeConfig(Config):
    def __init__(self, file, agentParameters, step):
        self.agentParameters = agentParameters
        self.step = step
        # reads file and returns a x and y cord list as well as polygon object
        self.parseFile(file)
        # flat cords are the gps cords mapped to a 2d plane, with no rotaiton this is UTM
        # print("boundary cords in utm")
        # print(self.flatCords)

        # make the polygon overlay
        self.buildPolygonGrid()
        # build map from linear index to global 2d location
        self.buildWorld()

        # remove points outside polygon
        self.polyPrune()
        print("global indices in state space")
        print(self.stateSpace)
        print('size of the state space', len(self.stateSpace))

        # get agent parameters
        self.setAgentParameters()

        # build transitions and costmaps
        super(ShapeConfig, self).__init__()
        # slice transition and costmap to only the valid states
        self.Ts = self.Ts[np.ix_(self.stateSpace, self.stateSpace)]

    def setAgentParameters(self):
        # base point
        if self.agentParameters is None:
           baseIdx = self.stateSpace[0]
           self.nAgent = 0
        else:
            # agent init
            self.maxTime = self.agentParameters["maxTime"]
            self.initAgent = np.array(self.agentParameters["initPos"])
            self.nAgent = len(self.initAgent)
            baseIdx = self.stateSpace[self.agentParameters["base"]]
        self.base = ind2sub(baseIdx, self.worldSize)

    def parseFile(self, file, longLat=False):
        print(file)
        # parse file
        with open(file) as csvfile:
            data = [(line[1], line[2]) for line in csv.reader(csvfile, delimiter=',')]
            # toss 1st line and convert to float
            self.GPSData = [tuple(map(float, line)) for line in data[1:]]
        # convert to utm
        if longLat:
            # assumes the file is in long, lat
            UTMData = [utm.from_latlon(cords[1], cords[0]) for cords in self.GPSData]
        else:
            # assumes the file is in lat, long
            UTMData = [utm.from_latlon(cords[0], cords[1]) for cords in self.GPSData]

        self.UTMZone = UTMData[0][2:]
        self.flatCords = np.array([[data[0], data[1]] for data in UTMData])

    def buildPolygonGrid(self):
        # build the polygon object
        # make the grid overlay and save the sizes as space 2D and 1D
        self.poly = Polygon(self.flatCords)
        # for i in range(len(splits)-1):
        #    self.polys.append(Polygon(self.UTMCords[splits[i]:splits[i+1]]))
        minx, miny, maxx, maxy = self.poly.bounds
        print('boundary extends in meters', (maxx - minx), (maxy - miny))
        self.xGrid = np.linspace(minx, maxx, int((maxx - minx) / self.step))
        self.yGrid = np.linspace(miny, maxy, int((maxy - miny) / self.step))
        self.nX = len(self.xGrid)
        self.nY = len(self.yGrid)
        # world objects
        self.worldSize = (self.nX, self.nY)
        self.nStates = int(np.prod(self.worldSize))

    def inPoly(self, polys, point):
        # checks if point (tuple) is in the polygon
        pt = Point(point)
        return all([poly.contains(pt) for poly in polys])

    def polyPrune(self):
        # prune for containment
        if self.zoneIdx == -1:
            # ignore the zone splits
            polys = [self.poly]
        else:
            polys = [self.poly, self.zonePolys[self.zoneIdx]]

        self.stateSpace = [s for s in range(self.nStates) if self.inPoly(
                                          polys, self.world[:, s])]

    def plotPolygon(self, ax):
        x = [point[0] for point in self.poly.exterior.coords]
        y = [point[1] for point in self.poly.exterior.coords]
        ax.plot(x, y, color='k')

    def plotZones(self, ax):
        colors = ['b', 'g', 'r', 'm', 'c', 'y']
        for zone, color in zip(self.zonePolys, colors):
            x = [point[0] for point in zone.exterior.coords]
            y = [point[1] for point in zone.exterior.coords]
            ax.plot(x, y, color=color)

    def plotKeyPonts(self, ax):
        for key, val in self.keyPoints.items():
            easting, northing, _, _ = utm.from_latlon(val[0], val[1])
            UTMCords = np.array([easting, northing])
            # ROTATE THE DAMN CORDS
            UTMCordsRot = np.dot(self.R, UTMCords.T)
            # print(UTMCordsRot)
            ax.scatter(*UTMCordsRot[0:2], color='k')
            ax.annotate(key, xy=UTMCordsRot[0:2], xycoords='data')

    def plotAgents(self, ax):
        colors = ['b', 'g', 'r', 'm', 'c', 'y']
        for agentIdx, color in zip(self.initAgent, colors):
            worldIdx = self.stateSpace[agentIdx]
            pt = self.world[:, worldIdx]
            ax.scatter(pt[0], pt[1], color=color)

    def UTM2LatLong(self, utmCord):
        return utm.to_latlon(utmCord[0], utmCord[1], *self.UTMZone)

    def plot(self, ax, showGrid=True):
        if showGrid:
            super(ShapeConfig, self).plot(ax)
        self.plotPolygon(ax)
        if self.zoneIdx != -1:
            self.plotZones(ax)
        self.plotKeyPonts(ax)
        self.plotAgents(ax)

    def writeInfo(self, filepath):
        # writes the configuration information of the test
        super(ShapeConfig, self).writeInfo(filepath)
        with open(self.outfile, 'a') as f:
            f.write('\nstep\n')
            f.write(str(self.step))


if __name__ == '__main__':
    dataDir = "../data/baylands"
    cordsFile = "outer.csv"
    file = os.path.join(dataDir, cordsFile)
    config = ShapeConfig(file, step=20)

    # plot
    fig, ax = plt.subplots()
    config.plot(ax)
    plt.show()
