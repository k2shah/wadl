import numpy as np
import numpy.random as rand
import numpy.linalg as la
import os as os
# plot
import matplotlib.pyplot as plt
# lib
try:
    from .utils import *
except (SystemError, ImportError):
    from utils import *


class Config(object):
    def __init__(self, typ=None):
        self.dim = 2
        self.solTime = 0
        if typ == 'small':
            self.maxTime = 20
            # world init
            self.worldSize = (6, 6)
            self.xGrid = np.linspace(0, 100, self.worldSize[0])
            self.yGrid = np.linspace(0, 100, self.worldSize[1])
            self.nX = len(self.xGrid)
            self.nY = len(self.yGrid)
            # number of states
            self.nStates = int(np.prod(self.worldSize))
            self.stateSpace = range(self.nStates)
            self.buildWorld()

            # robot init
            self.base = (0, 0)

            self.initAgent = [(0, 0),
                              (3, 0),
                              (6, 0),
                              (7, 0)]
            self.nAgent = len(self.initAgent)
            self.nStates = int(np.prod(self.worldSize))

        # build helper objects
        self.buildTransition()
        self.buildCostmap()

    def buildTransition(self):
        # make transition matrix
        self.Ts = np.eye(self.nStates, dtype=int)
        # connective graph node to list of connected nodes
        self.con = []
        for s in range(self.nStates):
            adj = []
            i, j = ind2sub(s, self.worldSize)
            if i - 1 >= 0:
                adj.append(sub2ind((i-1, j), self.worldSize))  # left
            if i + 1 < self.nX:
                adj.append(sub2ind((i+1, j), self.worldSize))  # right
            if j - 1 >= 0:
                adj.append(sub2ind((i, j-1), self.worldSize))  # bottom
            if j + 1 < self.nY:
                adj.append(sub2ind((i, j+1), self.worldSize))  # top

            self.Ts[s, adj] = len(adj)*[1]
            self.con.append(adj)

    def buildWorld(self):
        self.world = np.zeros((2, self.nStates))
        for s in range(self.nStates):
            xIdx, yIdx = ind2sub(s, self.worldSize)
            self.world[:, s] = [self.xGrid[xIdx],
                                self.yGrid[yIdx]]

    def buildCostmap(self):
        self.costmap = np.array([l1(self.base, ind2sub(s, self.worldSize))
                                 for s in self.stateSpace])

    def plot(self, ax):
        for i, node in enumerate(self.stateSpace):
            ax.scatter(*self.world[:, node], color='k', s=.1)
            for j, adj in enumerate(self.con[node]):
                if adj in self.stateSpace:
                    ax.plot([self.world[0, node], self.world[0, adj]],
                            [self.world[1, node], self.world[1, adj]],
                            color='k')

    def setSolTime(self, solTime):
        # store the solution time of the solve
        self.solTime = solTime

    def writeInfo(self, filepath):
        # writes the configuration information of the test
        if not os.path.exists(filepath):
            os.makedirs(filepath)
        self.outfile = os.path.join(filepath, 'info.txt')
        with open(self.outfile, 'w') as f:

            f.write('\nWorld Size\n')
            f.write(str(self.worldSize))

            f.write('\nbase pt\n')
            f.write(str(self.base))

            f.write('\nmax time\n')
            f.write(str(self.maxTime))

            f.write('\nsolution  time\n')
            f.write(str(self.solTime))

            f.write('\ninitial agent positions\n')
            f.write(np.array2string(self.initAgent, formatter={
                                    'float_kind': lambda x: "%.2f" % x}))


if __name__ == '__main__':
    config = Config('small')
    fig, ax = plt.subplots()
    config.plot(ax)
    plt.show()
