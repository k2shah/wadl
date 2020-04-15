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
from shapely.geometry import Point
# lib
from utils import *
from fence import Fence
from agent import Agents


class Config(Fence):
    def __init__(self, file, agents, step):
        super(Config, self).__init__(file)
        self.dim = 2
        self.solTime = None
        # store configuations
        self.agents = agents
        self.step = step

        # build grid graph
        self.buildLatice(self)
        self.buildGraph(self)
        # build helper objects
        # self.buildTransition()
        # self.buildCostmap()

    def buildGrid(self, R=0):
        # get bounds
        minx, miny, maxx, maxy = poly.bounds
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
                if self.poly.contains(Point(x,y)):
                    self.world[(i,j)] = (x, y)
                else:
                    self.graph.remove_node((i,j))



    def polyPrune(self, point):
        # prune for containment
        pt = Point(point)
        return 

    def plot(self, ax):
        # plot the geofence with grid overlay
        # plot fence
        super(Config, self).plot(ax, color='k')
        # plot grid
        # plot nods
        for node in self.graph.nodes:
            ax.scatter(*self.world[node],
                       color='k', s=.1)
    #     for i, node in enumerate(self.stateSpace):
    #         ax.scatter(*self.world[:, node], color='k', s=.1)
    #         for j, adj in enumerate(self.con[node]):
    #             if adj in self.stateSpace:
    #                 ax.plot([self.world[0, node], self.world[0, adj]],
    #                         [self.world[1, node], self.world[1, adj]],
    #                         color='k')

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
    starts = [0, 1]
    maxPath = 40
    step = 40
    agents = Agents(starts, maxPath)

    config = Config('croz_west', agents, step)
    fig, ax = plt.subplots()
    config.plot(ax)

    plt.show()
