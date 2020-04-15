#!/usr/bin/python3
import os
import csv
# math
import numpy as np
#
import matplotlib.pyplot as plt
# gis
import utm
from shapely.geometry import Polygon


class Fence(object):
    """Holds the gps cords of the boundary of the area"""

    def __init__(self, file):
        """ on init parse the cvs cords file
            parser assumes "lat,  lng"
        """
        self.dataPath = os.path.join(os.path.dirname( __file__ ), '..', 'data', 'geofences')
        self.parseFile(file)
        self.poly = Polygon(self.UTMCords)
        minx, miny, maxx, maxy = self.poly.bounds
        print('boundary extends in meters', (maxx - minx), (maxy - miny))

    def parseFile(self, file):
        # parse file as CSV
        # stores the gps cords, utm cords, and utm zones
        CSVfile = os.path.join(self.dataPath, file+".csv")
        with open(CSVfile, 'r') as csvfile:
            data = [(line[1], line[2])
                    for line in csv.reader(csvfile, delimiter=',')]
        # toss 1st line and convert to float
        GPSData = [list(map(float, line)) for line in data[1:]]
        # convert to utm
        UTMData = [utm.from_latlon(cords[0], cords[1]) for cords in GPSData]
        # store coridinate information
        self.UTMZone = UTMData[0][2:]
        # print(self.UTMZone)
        self.UTMCords = np.array([[data[0], data[1]] for data in UTMData])
        self.GPScords = np.array(GPSData)

    def plot(self, ax, color='m'):
        # plots are always in utm
        ax.plot(*self.poly.exterior.xy, color=color)


class Areas(object):
    """holds the data from a KML file"""
    def __init__(self, file):
        self.areas = dict()
        print(file)
        self.parseFile(file)

    def parseFile(self, file):
        # parse the cords from the KML file
        nameTag = "<name>"
        cordsTag = "<coordinates>"
        with open(file, 'r') as f:
            for line in f:
                if nameTag in line:
                    name = self.stripXML(line)
                    # print(name)
                    self.areas[name] = []
                if cordsTag in line:
                    cords = f.readline()

                    cords = cords.strip()
                    cords = cords.split(" ")
                    self.areas[name].append(
                                    np.array([list(map(float, c.split((","))))
                                              for c in cords]))
                    # print(self.areas[name])

    def stripXML(self, string):
        # strips the "<>" and "/<>" from a string
        temp = string.split('>')[1]
        return temp.split('<')[0]

    def plot(self, ax):
        for areaKey in self.areas:
            for ring in self.areas[areaKey]:
                ax.plot(ring[:, 0], ring[:, 1], 'k')


if __name__ == '__main__':
    # move this test code later
    fence = Fence("croz_rook")
    fig, ax = plt.subplots()
    print(fig)
    fence.plot(ax)
    print(sum(fence.UTMCords))
    print(hash(fig))
    plt.show()
