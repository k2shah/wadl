#!bin/bash/python3
# import warnings as warn
import os
import csv
import json
import glob
import time
# import sys
# gis
import utm
# math
import numpy as np
import numpy.linalg as la
# plot
import matplotlib.pyplot as plt
import mpl_toolkits.mplot3d.axes3d as axes3d
# lib
try:
    from .utils import *
    from .fence import Fence, Areas
except (SystemError, ImportError):
    from utils import *
    from fence import Fence, Areas


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
        self.cameraSize = (55, 73)  # m
        l, w = self.cameraSize
        self.cameraBox = np.array([[l/2., w/2.],
                                   [l/2., -w/2.],
                                   [-l/2., -w/2.],
                                   [-l/2., w/2.],
                                   [l/2., w/2.]])
        self.speed = 4.0  # m/s
        self.triggerInt = 2  # secs
        self.interpRoute()

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

    def interpRoute(self):
        self.xpath = []
        self.ypath = []
        for i, action in enumerate(self.actions):
            if action:
                # 1st cords cuz fwd path progress
                if len(self.xpath) == 0:
                    cords = utm.from_latlon(self.cords[i, 1], self.cords[i, 0])
                    self.xpath.append(cords[0])
                    self.ypath.append(cords[1])
                # rest of cords
                cords = utm.from_latlon(self.cords[i+1, 1], self.cords[i+1, 0])
                self.xpath.append(cords[0])
                self.ypath.append(cords[1])
        self.pathLen = [0]
        self.UTMZone = cords[2:]

        # get diffs
        xdiff = np.diff(self.xpath)
        ydiff = np.diff(self.ypath)
        # calculate path lenght at each section
        self.arcLen = np.cumsum([0] +
                                [la.norm([dx, dy])
                                 for dx, dy in zip(xdiff, ydiff)])
        # interp at speed * photo interval
        # arc lenght is the lambda for x,y = curve(lambda)
        interpols = np.arange(0, self.arcLen[-1],
                              self.speed*self.triggerInt)
        self.xinterp = np.interp(interpols, self.arcLen, self.xpath)
        self.yinterp = np.interp(interpols, self.arcLen, self.ypath)
        # get vectors for photo alignments\
        self.dirInterp = [[dx, dy] for dx, dy
                          in zip(np.diff(self.xinterp),
                                 np.diff(self.yinterp))]
        # copy the last element for the last image
        self.dirInterp.append(self.dirInterp[-1])

    def pt2gBox(self, p, v):
        # returns the ground ppints of the image corners
        alpha = np.arctan2(v[1], v[0])
        R90 = rot2D(alpha)

        cameraRot = np.dot(R90, self.cameraBox.T).T.tolist()
        camera = [utm.to_latlon(p[0] + z[0], p[1] + z[1], *self.UTMZone)
                  for z in cameraRot]

        return camera

    def plotInterp(self, ax, color=(.5625, 0, 0, .6)):
        for x, y, v in zip(self.xinterp, self.yinterp, self.dirInterp):
            lat, lng = utm.to_latlon(x, y, *self.UTMZone)
            # plot the camera
            camera = np.array(self.pt2gBox([x, y], v))
            ax.fill(camera[:, 1], camera[:, 0],
                    color=color)
            # plot the point
            # ax.scatter(lng, lat, c='c', s=2)
            # plt.draw()
            # plt.pause(.00000001)

    def plotRoute(self, ax):
        # plots the route
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
                    c=col, s=2)

    def plot(self, ax):
        # runs all the plot subruts
        # self.plotRoute(ax)
        self.plotInterp(ax)


def main(mission):
    # get geo fence
    fenceFileCroz = '../data/croz_geofence/croz_west_3.csv'
    crozFence = Fence(fenceFileCroz)
    fenceFileRook = '../data/croz_east/croz_rook_3.csv'
    rookFence = Fence(fenceFileRook)
    # get areas
    file = "../data/croz_geofence/areas.kml"
    crozAreas = Areas(file)

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
    fig = plt.figure(figsize=(16, 9))
    # ax = fig.add_subplot(1, 1, 1, projection='3d')
    ax = fig.add_subplot(111)
    crozFence.plot(ax)
    rookFence.plot(ax)
    crozAreas.plot(ax)

    # build route sequence
    routeSeq = [(int(r.split('-')[0].strip('r')), r)
                for r in list(routes.keys())]
    routeSeq.sort()
    print(routeSeq)
    cm = plt.cm.get_cmap('jet', len(routeSeq))
    alpha = .6
    for rnum, key in routeSeq:
        plt.title(key)
        color = cm(rnum-1)
        color = (*color[0:3], alpha)
        routes[key].plotInterp(ax, color=color)
        plt.draw()
        plt.pause(.0000001)
    plt.show()


if __name__ == '__main__':
    missionDir = "../missions"
    # missionName = "croz2-fine"
    missionName = "croz3-full"
    missionPath = os.path.join(missionDir, missionName)
    main(missionPath)
