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
    def __init__(self, pathDir):
        self.pathDir = pathDir
        self.parseFile()

    def parseFile(self):
        pathFiles = glob.glob(os.path.join(self.pathDir, "routes/*"))
        for file in pathFiles:
            self.cords = dict()
            print(file)
            with open(file) as csvfile:
                for line in csv.reader(csvfile, delimiter=','):
                    try:
                        self.cords[(line[0], line[1])] += 1
                    except KeyError as e:
                        self.cords[(line[0], line[1])] = 1

            routeEff = self.calcEff()
            self.writeEff(file, routeEff)

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
