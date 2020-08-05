# gen
import os as os
# math
import numpy as np
# graph
import networkx as nx
# plot
import matplotlib.pyplot as plt
# gis
import utm
from shapely.geometry import Polygon, Point
# lib
from wadl.lib.utils import rot2D
from wadl.lib.fence import Fence
from wadl.lib.route import RouteSet


class Maze(Fence):
    def __init__(self,
                 file,
                 step=40,
                 rotation=0,
                 home=None,
                 flightParams=None):
        super(Maze, self).__init__(file)
        # set parameters
        # grid parameters
        self.theta = rotation
        self.step = step
        # build grid graph
        self.buildGrid()
        self.nNode = len(self.graph)
        print(f"\tgenerated maze with {self.nNode} nodes")
        # UAV path parameters
        self.home = home
        self.nNode = len(self.graph)  # store size of nodes
        self.routeSet = RouteSet(self.home, self.UTMZone, flightParams)

    def __len__(self):
        # number of nodes
        return len(self.graph)

    # Grid setup

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
        self.xWorld = np.arange(minx, maxx, self.step)
        self.yWorld = np.arange(miny, maxy, self.step)

        self.nX = len(self.xWorld)
        self.nY = len(self.yWorld)
        # build graph
        self.graph = nx.grid_graph(dim=[self.nY, self.nX])
        # prune points outside polygon
        for i, x in enumerate(self.xWorld):
            for j, y in enumerate(self.yWorld):
                if rotatedPoly.contains(Point(x, y)):
                    utmCord = self.R.T @ np.array([x, y])
                    # store utm cord in graph
                    self.graph.nodes[(i, j)]['UTM'] = utmCord
                else:
                    self.graph.remove_node((i, j))

        # save the index of each node
        for i, node in enumerate(self.graph):
            self.graph.nodes[node]['index'] = i

    # write
    def write(self, filePath):
        self.taskName = self.name + f'_s{self.step}_n{self.nAgent}'
        taskDir = os.path.join(filePath, self.taskName)
        if not os.path.exists(taskDir):  # make dir if not exists
            os.makedirs(taskDir)
        # write maze configuration information
        self.writeInfo(taskDir)
        # write paths as GPS csv files.
        pathDir = os.path.join(taskDir, "paths")
        if not os.path.exists(pathDir):  # make dir if not exists
            os.makedirs(pathDir)
        self.writePaths(pathDir)
        # save the figure
        fig, ax = plt.subplots(figsize=(16, 16))
        self.plot(ax)
        plt.axis('square')
        plotName = os.path.join(taskDir, "routes.png")
        plt.savefig(plotName, bbox='tight', dpi=50)

    def writeInfo(self, filePath):
        # writes the Maze information of the test
        outFile = os.path.join(filePath, "info.txt")
        with open(outFile, 'w') as f:

            f.write('\nGrid size\n')
            f.write(str(self.nNode))

            f.write('\nPath limit\n')
            f.write(str(self.limit))

            f.write('\nSolution time (min)\n')
            f.write(str(self.solTime))

            f.write('\nInitial agent positions\n')
            for start in self.starts:
                f.write(f"{start}\n")

    def writePaths(self, pathDir):
        pass

    def writeGrid(self, outFile, UTM=True):
        # writes the grid to file
        if UTM:
            with open(outFile, 'w') as f:
                for node in self.graph:
                    cords = self.graph.nodes[node]["UTM"]
                    gps = utm.to_latlon(*cords, *self.UTMZone)
                    cordStr = str(cords[0]) + ", " + str(cords[1]) + "," +\
                        str(gps[0]) + ", " + str(gps[1]) + "\n"
                    f.write(cordStr)
        else:
            raise NotImplementedError()

    # plot
    def plotNodes(self, ax, color='k', nodes=None):
        # plot nodes
        if nodes is None:
            nodes = self.graph.nodes

        for node in nodes:
            ax.scatter(*self.graph.nodes[node]["UTM"],
                       color=color)

    def plotEdges(self, ax):
        # plot edges
        for e1, e2 in self.graph.edges:
            line = np.array([self.graph.nodes[e1]["UTM"],
                             self.graph.nodes[e2]["UTM"]])
            ax.plot(line[:, 0], line[:, 1],
                    color='k', linewidth=1)

    def plotRoutes(self, ax):
        cols = iter(plt.cm.rainbow(np.linspace(0, 1, len(self.routeSet))))
        for route in self.routeSet:
            route.plot(ax, color=next(cols))

    def plot(self, ax, showGrid=False):
        # plot the geofence with grid overlay
        # plot fence
        super(Maze, self).plot(ax, color='r')

        # plot maze
        if showGrid:
            # self.plotNodes(ax)
            self.plotEdges(ax)
        self.plotRoutes(ax)
