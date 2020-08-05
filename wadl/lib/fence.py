#!/usr/bin/python3
import csv
# math
import numpy as np
# gis
import utm
from shapely.geometry import Polygon


class Fence(object):
    """Holds the gps cords of the boundary of the area"""

    def __init__(self, file):
        """ on init parse the cvs cords file
            parser assumes "lat,  lng"
            file is abs path file
        """
        self.file = file
        # get name of area
        name = file.split('\\')[-1]
        self.name = name.split('.csv')[0]
        # parse file
        print("\nReading coordinate file {:s}".format(file))
        self.parseFile(file)
        # build polygon
        self.poly = Polygon(self.UTMCords)
        # find bounding box
        minx, miny, maxx, maxy = self.poly.bounds
        print(f"{self.name}: extends in meters {maxx - minx} by {maxy - miny}")

    def parseFile(self, file):
        # parse file as CSV
        # stores the gps cords, utm cords, and utm zones
        if ".csv" in file:
            CSVfile = file
        else:
            CSVfile = file + ".csv"
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
        self.GPSCords = np.array(GPSData)

    def plot(self, ax, color='m'):
        # plots are always in utm
        ax.plot(*self.poly.exterior.xy, color=color)
        # place label somewhere
        minx, miny, maxx, maxy = self.poly.bounds
        placement = ((minx+maxx)/2, maxy)
        ax.annotate(self.name, xy=placement)


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
