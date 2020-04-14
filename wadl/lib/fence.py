#!/usr/bin/python3
import os
import csv
# math
import numpy as np
# gis
import utm
from shapely.geometry import Point, Polygon
from shapely.wkb import loads


class Fence(object):
    """Holds the gps cords of the boundary of the area"""

    def __init__(self, file, lngLat=False):
    	""" on init parse the cvs cords file
    	    parser assumes "lat,  lng"
    	    can parse "lng, lat" if kwarg lngLat = True
    	"""
        self.parseFile(file, lngLat)
        self.border = self.makePolygon()

    def parseFile(self, file):
        # parse file as CSV
        with open(file, 'r') as csvfile:
            data = [(line[1], line[2])
                    for line in csv.reader(csvfile, delimiter=',')]
        # toss 1st line and convert to float
        GPSdata= [list(map(float, line)) for line in data[1:]]
        # convert to utm
        if longLat:
            # assumes the file is in long, lat
            UTMData = [utm.from_latlon(cords[1], cords[0]) for cords in self.GPSData]
        else:
            # assumes the file is in lat, long
            UTMData = [utm.from_latlon(cords[0], cords[1]) for cords in self.GPSData]
        # store coridinate information
        self.UTMZone = UTMData[0][2:]
        # print(self.UTMZone)
        self.UTMCords = np.array([[data[0], data[1]] for data in UTMData])
        self.GPScords = np.array(GPSData)

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
    # move this test code later
    fence = 
