#!/usr/bin/python3
import os
import csv
# math
import numpy as np
# gis
import utm


class Fence(object):
    """Holds the gps cords of the boundary of the area"""

    def __init__(self, file):
        self.parseFile(file)

    def parseFile(self, file):
        # parse file as CSV
        with open(file, 'r') as csvfile:
            data = [(line[1], line[2])
                    for line in csv.reader(csvfile, delimiter=',')]
        # toss 1st line and convert to float
        self.GPScords = [list(map(float, line)) for line in data[1:]]
        # convert to utm
        # assumes the file is in long, lat (x,y)
        UTMData = [utm.from_latlon(cords[1], cords[0])
                   for cords in self.GPScords]
        self.UTMZone = UTMData[0][2:]
        # print(self.UTMZone)
        self.flatCords = np.array([[data[0], data[1]] for data in UTMData])
        self.GPScords = np.array(self.GPScords)

    def plot(self, ax, color='m'):
        ax.plot(self.GPScords[:, 0], self.GPScords[:, 1],
                c=color)


class Areas(object):
    """holds the areas from a KML file"""
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
    file = "../data/croz_geofence/areas.kml"
    areas = Areas(file)
