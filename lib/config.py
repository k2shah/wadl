import numpy as np
import numpy.random as rand
import numpy.linalg as la
import os as os
#lib
from lib.utils import *

class Config:
    def __init__(self, typ='small'):
        if typ == 'small':
            self.maxTime = 200
            self.worldSize = (15, 10)
            self.dim = 2

            self.base = (0,0)

            self.initAgent = [(0, 0),
                              (3, 0),
                              (6, 0),
                              (7, 0)]
            self.nAgent = len(self.initAgent)



        #build helper objects
        self.buildTransition()
        self.buildWorld()
        self.buildCostmap()

    def buildTransition(self):
        #number of states
        self.S = int(np.prod(self.worldSize))
        # make transition matrix
        self.Ts = np.eye(self.S) * .5
        for i in range(self.S):
            for j in range(i):
                inp = np.unravel_index(j, (self.worldSize), order="F")
                out = np.unravel_index(i, (self.worldSize), order="F")
                if l1(inp, out) == 1:
                    self.Ts[i, j] = 1

        self.Ts += self.Ts.T  # some leet hacks

    def buildWorld(self):
        self.world = np.zeros((self.dim, self.S))
        idx = 0
        for j in range(self.worldSize[1]):
            for i in range(self.worldSize[0]):
                # set x and y values of the world to make a look up from linear idx to cord
                self.world[0, idx] = i
                self.world[1, idx] = j

    def buildCostmap(self):
        self.costmap = np.array([l1(self.base, ind2sub(s, self.worldSize))
                                 for s in range(self.S)])



    def writeInfo(self, filepath):
        # writes the configuration information of the test
        if not os.path.exists(filepath):
            os.makedirs(filepath)
        outfile = os.path.join(filepath, 'info.txt')
        # with open(outfile, 'w') as f:
        #
        #     # f.write('\nWorld Size\n')
        #     # f.write(np.array2string(self.worldSize, formatter={
        #     #                         'float_kind': lambda x: "%.2f" % x}))
        #
        #     # f.write('\ninitial agent positions\n')
        #     # f.write(np.array2string(self.initAgent, formatter={
        #     #                         'float_kind': lambda x: "%.2f" % x}))

