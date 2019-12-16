#!bin/bash/python3
# import warnings as warn
import os
import csv
import json
import glob
# import sys
# import time
# gis
import utm
# math
import numpy as np
# plot
import matplotlib.pyplot as plt
import mpl_toolkits.mplot3d.axes3d as axes3d


class Route(object):
    """holds the information of a single UGCS route"""

    def __init__(self, KMLfile, JSONdata):
        # get the route data from the kml and json
        self.parseKML(KMLfile)
        self.readJSON(JSONdata)
        # check the lenght of the paths
        if len(self.actions) != (self.cords.shape[0]-1):
            print(KMLfile)
            print(len(self.actions))
            print(self.cords.shape)
            # raise RuntimeError("path lengths do not mathch: {:s}".format(
            #       KMLfile))
        self.cameraSize = (2, 3)
        self.speed = 4.0

    def parseKML(self, KMLfile):
        # parse KMLfile
        cordTag = "coordinates"
        with open(KMLfile) as f:
            for line in f:
                if cordTag in line:
                    # cut out html tags
                    data = line.split(">")[1]
                    data = data.split("<")[0]
                    # split at each space
                    data = data.split(" ")
                    break
        # extract cords as LNG LAT ALT (AGL)
        self.cords = np.array([list(map(float, line.split((","))))
                               for line in data])

    def readJSON(self, JSONdata):
        self.actions = [wp["actions"] != [] for wp in JSONdata["segments"]]

    def plotRoute(self, ax):
        for i, action in enumerate(self.actions):
            if i < 1 or i > (len(self.actions)-2):
                # skip the 1st and last fe
                continue
            if action:
                col = "r"
            else:
                col = "b"

            ax.plot(self.cords[i:i+2, 0],
                    self.cords[i:i+2, 1],
                    c=col)

    def plot(self, ax):
        # plots the route
        self.plotRoute(ax)


class Fence(object):
    """Holds the gps cords of the boundary of the area"""

    def __init__(self, file, longLat=True):
        print(file)
        # parse file
        with open(file) as csvfile:
            data = [(line[1], line[2])
                    for line in csv.reader(csvfile, delimiter=',')]
            # toss 1st line and convert to float
            self.GPScords = [list(map(float, line))
                             for line in data[1:]]
        # convert to utm
        if longLat:
            # assumes the file is in long, lat
            UTMData = [utm.from_latlon(cords[1], cords[0])
                       for cords in self.GPScords]
        else:
            # assumes the file is in lat, long
            UTMData = [utm.from_latlon(cords[0], cords[1])
                       for cords in self.GPScords]
        self.UTMZone = UTMData[0][2:]
        print(self.UTMZone)
        self.flatCords = np.array([[data[0], data[1]] for data in UTMData])
        self.GPScords = np.array(self.GPScords)

    def plot(self, ax):
        ax.plot(self.GPScords[:, 0], self.GPScords[:, 1],
                c='g', linewidth=.5)


def main(mission):
    # get geo fence
    fenceFile = '../data/croz_geofence/croz_west_3.csv'
    crozFence = Fence(fenceFile)

    # get route files
    kmlPath = os.path.join(mission, "*.kml")
    kmlFiles = glob.glob(kmlPath)

    # read json
    jsonFile = mission + ".json"
    with open(jsonFile) as file:
        jsonData = json.load(file)
    # make route catalog name : route(datam kml)
    routes = dict()
    for routeData in jsonData["mission"]["routes"]:
        routeName = routeData["name"]
        KMLfile = os.path.join(mission, routeName+".kml")
        if os.path.exists(KMLfile):
            routes[routeData["name"]] = Route(KMLfile, routeData)
        else:
            print("kml file does not exist: {:s}".format(routeName))

    # plot stuff
    fig = plt.figure(figsize=(25, 16))
    # ax = fig.add_subplot(1, 1, 1, projection='3d')
    ax  = fig.add_subplot(111)
    crozFence.plot(ax)


    for key in routes:
        routes[key].plot(ax)

    plt.show()


if __name__ == '__main__':
    missionDir = "../missions"
    missionName = "croz2-fine"
    missionPath = os.path.join(missionDir, missionName)
    main(missionPath)
