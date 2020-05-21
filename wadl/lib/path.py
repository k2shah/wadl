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


class Path(object):
    """docstring for Path"""
    def __init__(self, cords, keyPoints = None):
        self.keyPoints = keyPoints
        self.GPScords = [] # cords in GPS
        self.UTMcords = [] # cord in UTM
        self.setUTM(cords)

    def setUTM(self, cords):
        self.UTMcords = np.array(cords)

    def setGPS(self, cords):
        self.UTMcord = np.array(cords)

    def setKeypoints(self, keyPoints):
        self.keyPoints = keyPoints

    def __len__(self):
        return self.UTMcords.shape[0]

    def __repr__(self):
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
        ax.plot(self.UTMcords[:-1, 0], self.UTMcords[:-1, 1])



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
