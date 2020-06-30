# gen 
import os as os
import time as time
# math
import numpy as np 
import numpy.random as rand
import numpy.linalg as la
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
from wadl.lib.path import Path

class Maze(Fence):
    def __init__(self, file, 
                 starts=[(0,0)],
                 step=40, limit=None,
                 rotation=0):         
        super(Maze, self).__init__(file)
        # set parameters
        self.dim = 2
        self.solTime = None
        self.solved = False
        # grid parameters
        self.theta = rotation
        self.step = step
        # build grid graph
        self.buildGrid()

        # uav parameters
        self.starts = starts
        self.nAgent = len(starts)
        self.paths = [None] * self.nAgent
        self.nNode = len(self.graph)# store size of nodes
        self.limit = limit if limit is not None else self.nNode + 5 # default: buffer lenght by 6 
      
        # find global start location from local start passed in
        self.findGlobalStart()
       
        # create full name of maze
        self.taskName = self.name + f'_s{step}_n{self.nAgent}_t{self.limit}'
        print(f"Generated maze graph with {self.nNode} nodes")

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
        # make world {(node) -> (utm)}
        self.world = dict()
        # prune points outside polygon
        for i, x in enumerate(self.xWorld):
            for j, y in enumerate(self.yWorld):
                if rotatedPoly.contains(Point(x,y)):
                    self.world[(i,j)] = self.R.T @ np.array([x, y])
                else:
                    self.graph.remove_node((i,j))


        # save the index of each node
        for i, node in enumerate(self.graph):
            self.graph.nodes[node]['index'] = i

        # calculate the offset from the lower left node 
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


    # Solution 
    def solve(self, Solver):
        print(f"\nsolving maze {self.taskName}")
        startTime = time.time()
        self.solver = Solver(self)
        # solve the problems
        print(f"solving subproblems")
        self.solved, self.sols, self.solTime = self.solver.solve()
        if not self.solved:
            raise RuntimeError("problem failed")
        paths = []
        for sol in self.sols:
            # print(sol)
            paths.append([self.world[pt] for pt in sol])
        # make Path objects from the soltion
        self.paths = [Path(path) for path in paths]
        pathLenghts = [len(path) for path in self.paths]
        print(f"found {len(self.paths)} paths of lengths {pathLenghts}")

        #time the job
        mazeTime = time.time() - startTime
        print("total time: {:2.5f} sec".format(mazeTime))

    # write
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
        for i, path in enumerate(self.paths):
            pathFile = os.path.join(pathDir, str(i)+".csv")
            path.UTM2GPS(self.UTMZone)
            path.write(pathFile)

    def writeGrid(self, outFile, UTM=True):
        # writes the grid to file 
        if UTM:
            with open(outFile, 'w') as f:
                for node in self.graph:
                    cords = self.world[node]
                    gps = utm.to_latlon(*cords, *self.UTMZone)
                    cordStr = str(cords[0])+ ", " + str(cords[1]) + "," +\
                              str(gps[0]) + ", " + str(gps[1]) + "\n"
                    f.write(cordStr)

                

        else:
            raise NotImplementedError()

    def write(self, filePath):
        taskDir = os.path.join(filePath, self.taskName)
        if not os.path.exists(taskDir): # make dir if not exists
            os.makedirs(taskDir)
        # write maze configuration information
        self.writeInfo(taskDir)
        # write paths as GPS csv files.
        pathDir = os.path.join(taskDir, "paths")
        if not os.path.exists(pathDir): # make dir if not exists
            os.makedirs(pathDir)
        self.writePaths(pathDir)
        # save the figure
        fig, ax = plt.subplots(figsize=(16, 16))
        self.plot(ax)
        plotName = os.path.join(taskDir, "routes.png")
        plt.savefig(plotName, bbox='tight', dpi=50)

    # plot
    def plotNodes(self, ax, color='k', nodes=None):
        # plot nodes
        if nodes is None:
            nodes = self.graph.nodes

        for node in nodes:
            ax.scatter(*self.world[node],
                       color=color)

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

    def plotPaths(self, ax):
        if self.solved is True:
            nPaths = len(self.paths)
            cols = iter(plt.cm.rainbow(np.linspace(0,1,nPaths)))
            for path in self.paths:
                path.plot(ax, color = next(cols))

    def plot(self, ax, showGrid=False):
        # plot the geofence with grid overlay
        # plot fence
        super(Maze, self).plot(ax, color='r')

        # plot maze
        if showGrid:
            # self.plotNodes(ax)
            self.plotEdges(ax)
        self.plotStarts(ax)
        self.plotPaths(ax)

if __name__ == '__main__':
    starts = [(0,0),
              (1,1)]

    path = os.path.join(os.path.dirname( __file__ ), '..', 'data', 'geofences')
    file = os.path.join(path, "croz_west")
    
    absfile = os.path.abspath(file)
    maze = Maze(absfile, starts,
                    rotation=15)

    fig, ax = plt.subplots()
    maze.plot(ax, showGrid=True)
    plt.show()
