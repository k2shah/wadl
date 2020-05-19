import numpy as np
import numpy.random as rand
import numpy.linalg as la
import os as os
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


class Config(Fence):
    def __init__(self, file, starts,
                 step=40, maxPath=40):
        super(Config, self).__init__(file)
        self.dim = 2
        self.solTime = None
        # change when extended
        self.theta = 0
        # store configuations
        self.starts = starts
        # store defaults
        self.step = step
        self.maxPath = maxPath

        # build helper objects
        # build grid graph
        self.buildGrid()
        self.findGlobalStart()

    def rotateGrid(self):
        self.R = rot2D(np.radians(self.theta))
        cordsRotated = (self.R @ self.UTMCords.T).T
        return Polygon(cordsRotated)
        # self.R = np.eye(2)

    def buildGrid(self):
        # rotate cords
        rotatedPoly = self.rotateGrid()
        # get bounds
        minx, miny, maxx, maxy = rotatedPoly.bounds
        self.xWorld = np.linspace(minx, maxx, int((maxx - minx) / self.step))
        self.yWorld = np.linspace(miny, maxy, int((maxy - miny) / self.step))
        
        self.nX = len(self.xWorld)
        self.nY = len(self.yWorld)
        # build graph
        self.graph = nx.grid_graph(dim=[self.nY, self.nX])
        # make worldMap{(node) -> (utm)}
        self.world = dict()
        # prune points outside polygon
        for i, x in enumerate(self.xWorld):
            for j, y in enumerate(self.yWorld):
                if rotatedPoly.contains(Point(x,y)):
                    self.world[(i,j)] = self.R.T @ np.array([x, y])
                else:
                    self.graph.remove_node((i,j))

        self.findOffsets()

    def findOffsets(self):
        # finds cord offsets so bottom left corner is (0,0)
        self.offset = sorted(self.graph.nodes,
                             key=lambda x:(x[1],x[0]))[0]
    
    def findGlobalStart(self):
        # finds the global start of the agents using the relative start init
        # because adding tuples is silly
        self.globalStarts = [tuple(map(sum, zip(s, self.offset)))
                             for s in self.starts]
        for start in self.globalStarts:
            if start not in self.graph.nodes:
                raise KeyError('point not on graph', start)

        # check if points are in the graph

    def polyPrune(self, point):
        # prune for containment
        pt = Point(point)
        return 

    def plotNodes(self, ax):
        # plot nodes
        for node in self.graph.nodes:
            ax.scatter(*self.world[node],
                       color='k', s=5)

    def plotEdges(self, ax):
        # plot edges
        for e1, e2 in self.graph.edges:
            line = np.array([self.world[e1], self.world[e2]])
            ax.plot(line[:, 0], line[:, 1],
                    color='k', linewidth=1)

    def plotStarts(self, ax):
        # plot start locations
        for start in self.globalStarts:
            ax.scatter(*self.world[start],
                    color='b', s=10)


    def plot(self, ax):
        # plot the geofence with grid overlay
        # plot fence
        super(Config, self).plot(ax, color='r')

        # plot configuration
        #self.plotNodes(ax)
        self.plotEdges(ax)
        self.plotStarts(ax)

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

            f.write('\nsolution  time (min)\n')
            f.write(str(self.solTime))

            f.write('\ninitial agent positions\n')
            f.write(np.array2string(self.initAgent, formatter={
                                    'float_kind': lambda x: "%.2f" % x}))


if __name__ == '__main__':
    starts = [(0,0),
              (1,1)]

    config = Config('croz_west', starts)

    fig, ax = plt.subplots()
    config.plot(ax)
    plt.show()
