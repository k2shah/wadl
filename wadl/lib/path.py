#!bin/bash/python3
# import warnings as warn
import os
import csv
import json
import glob
import time
import warnings as warn
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
from wadl.lib.utils import *


class Path(object):
    """docstring for Path"""
    def __init__(self, cords, typ="UTM"):
        self.GPScords = [] # cords in GPS
        self.homePt = None
        self.UTMcords = [] # cords in UTM
        if typ== "UTM":
            self.setUTM(cords)
        elif typ=="GPS":
            self.setGPS(cords)
        else:
            raise RuntimeError("invalid type of coordinates")

    def setUTM(self, cords):
        self.UTMcords = cords

    def setGPS(self, cords):
        self.GPScord = cords

    def UTM2GPS(self, zone):
        # converts all the UTM cords to GPS
        self.GPScords = [utm.to_latlon(*cord, *zone) for cord in self.UTMcords]

    def GPS2UTM(self):
        # converts all the GPS cords to UTM
        self.UTMcords = [utm.from_latlon(*cord)[0:2] for cord in self.GPScords]

    def setHome(self, homePt):
        # homePT: (lat, long)
        # sets the route home at the home pt
        self.homePt = np.array(homePt)
        # finds the cloest pt on the route to the homePT
        (pt, idx) = min([(l2(homePt, pt), i) for i, pt in enumerate(self.GPScords)])
        # shift and wrap
        self.GPScords = self.GPScords[idx:] + self.GPScords[1:idx+1]
        # sync the utm 
        self.GPS2UTM()

    def __len__(self):
        # number of waypoints in path
        return len(self.UTMcords)

    def __repr__(self):
        #print the cords
        return print(self.UTMcords)
        
    def parseFile(self):
        pathFiles = glob.glob(os.path.join(self.pathDir, "routes/*"))
        for file in pathFiles:
            self.cords = dict()
            # print(file)
            with open(file) as csvfile:
                for line in csv.reader(csvfile, delimiter=','):
                    if line[2] != '50':
                        continue
                    cords = (line[0], line[1])
                    if cords in self.keyPoints:
                        continue
                    try:
                        self.cords[cords] += 1
                    except KeyError as e:
                        self.cords[cords] = 1
                try:
                    routeEff = self.calcEff()
                    print(file, ": ", routeEff)
                    self.writeEff(file, routeEff)
                except ZeroDivisionError as e:
                    print("invalid file: {:s}".format(file))

    def calcEff(self):
        nPts = 0
        nPaths = 0
        for keys in self.cords:
            nPaths += self.cords[keys]
            nPts += 1
        return nPts/nPaths

    def writeEff(self, routeFile, routeEff):
        infoFile = os.path.join(self.pathDir, "info.txt")
        if os.path.exists(infoFile):
            writeMode = 'a'
        else:
            writeMode = 'w'
        with open(infoFile, writeMode) as f:
            routeName = routeFile.split('/')[-1]
            f.write("\n{:s}: {:2.4f}".format(
                    routeName,
                    routeEff))

    def plot(self, ax, color='b'):
        # path
        cords = np.array(self.UTMcords)
        ax.plot(cords[:, 0], cords[:, 1], color=color)
        # start and end
        ax.scatter(cords[0, 0], cords[0, 1], color=color, marker='^')
        ax.scatter(cords[-2, 0], cords[-2, 1], color=color, marker='s')
        if self.homePt is not None:
            #plot the home point as a 'o'
            HomeUTMx, HomeUTMy  = utm.from_latlon(*self.homePt)[0:2]
            ax.scatter(HomeUTMx, HomeUTMy, color=color, marker='o')
            ax.plot([HomeUTMx, cords[0, 0]], [HomeUTMy, cords[0, 1]],
                     color=color, linestyle="--")


    def write(self, filename, **kwargs):
        # writes the trajectory as a txt file
        # Lat,Long,Alt,Speed,Picture,ElevationMap,WP,CameraTilt,UavYaw,DistanceFrom
        # set flight parameters
        spd =     kwargs["speed"]
        alt =     kwargs["altitude"]
        xferSpd = kwargs["xfer speed"]
        xferAlt = kwargs["xfer altitude"]
        xferAsc = kwargs["xfer ascend"]
        xferDes = kwargs["xfer descend"]
        landALt = kwargs["land altitude"]

        with open(filename, "w+") as f:
            # take off
            Hlat, Hlng = self.homePt
            f.write(f"{Hlat}, {Hlng}, {xferAlt}, {xferSpd},FALSE,,\n")
            # get higher above frist point, point camera down
            lat, lng = self.GPScords[0]
            f.write(f"{lat}, {lng}, {xferAlt}, {xferDes},FALSE,,,,90\n")
            # write the route to file
            for lat, lng in self.GPScords[:-1]:
                f.write(f"{lat}, {lng}, {alt}, {spd},FALSE,,\n")
            lat, lng = self.GPScords[-1]
            # last point to ascend to transfer
            f.write(f"{lat}, {lng}, {alt}, {xferAsc},FALSE,,\n")
            # get higher above last point, point camera fwd
            f.write(f"{lat}, {lng}, {xferAlt}, {xferSpd},FALSE,,,0\n")
            # return home
            f.write(f"{Hlat}, {Hlng}, {xferAlt}, {xferDes},FALSE,,1\n")
            f.write(f"{Hlat}, {Hlng}, {landALt}, {xferDes},FALSE,,1\n")


def main(pathDir):
    # get path files
    pathFiles = glob.glob(os.path.join(pathDir, "*/*/"))

    # read json
    # jsonFile = mission + ".json"
    for pathDir in pathFiles:
        Path(pathDir)


if __name__ == '__main__':
    pathDir = "../out"
    main(pathDir)
