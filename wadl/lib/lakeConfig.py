#!bin/bash/python3
# import warnings as warn
import os
import csv
import glob
# import sys
# import time
# math
import numpy as np
#graph 
import networkx as nx
# plot
import matplotlib.pyplot as plt
# gis
import utm
from shapely.geometry import Polygon, Point
# lib
from wadl.lib.utils import *
from wadl.lib.fence import Fence
from wadl.lib.config import Config


class LakeConfig(object):
    def __init__(self, starts,
                 step, maxPath=40):
        
        # overlay key points
        # self.keyPoints = {'p':     (-77.455917, 169.21753),
        #                   'c':     (-77.454753, 169.216886),
        #                   'bn':    (-77.44906,  169.22322),
        #                   'mle':   (-77.45362,  169.23247),
        #                   'fg':    (-77.459294, 169.245182)}

        dataDir = os.path.join("..", "data", "geofences", "mono_lake")
        files = glob.glob(os.path.join(dataDir, "*.csv"))
        print(files)
        self.configs = [Config(os.path.join("..", file).split(".csv")[0], starts, step=step) for file in files]



    


if __name__ == '__main__':
    step = 39
    config = LakeConfig([[0,0]], step=step)
    fig, ax = plt.subplots()
    for cfig in config.configs:
        cfig.plot(ax)
        
    plt.show()

