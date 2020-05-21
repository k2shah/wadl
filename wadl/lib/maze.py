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
        self.limit = limit if limit is not None else self.nNode + 2 # default: buffer lenght by 6 
      
        # find global start location from local start passed in
        self.findGlobalStart()
       
        # create full name of maze
        self.taskName = self.name + f'_s{step}_n{self.nAgent}_t{self.limit}'
        print(f"Generated maze graph with {self.nNode} nodes")

    def __len__(self):
        # number of nodes
        return len(self.graph)

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

    def plotPaths(self, ax):
        if self.solved is False:
            return
        cols = iter(['b', 'g', 'r', 'm'])
        for path in self.paths:
                path.plot(ax, color = next(cols))

    def plot(self, ax, showGrid=False):
        # plot the geofence with grid overlay
        # plot fence
        super(Maze, self).plot(ax, color='r')

        # plot maze
        if showGrid:
            self.plotNodes(ax)
            self.plotEdges(ax)
        self.plotStarts(ax)
        self.plotPaths(ax)

    def setSolTime(self, solTime):
        # store the solution time of the solve
        self.solTime = solTime

    def solve(self, solver):
        print(f"\nSolving maze {self.taskName}")
        problem = solver(self)
        # make Path objects from the soltion
        self.sols = problem.solve()
        paths = []
        for sol in self.sols:
            print(sol)
            paths.append([self.world[pt] for pt in sol])
        self.paths = [Path(path) for path in paths]
        pathLenghts = [len(path) for path in self.paths]
        print(f"Found {len(self.paths)} paths of lengths {pathLenghts}")
        self.solved = True

    def writeInfo(self, filepath):
        # writes the Mazeuration information of the test
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

    path = os.path.join(os.path.dirname( __file__ ), '..', 'data', 'geofences')
    file = os.path.join(path, "croz_west")
    
    absfile = os.path.abspath(file)
    maze = Maze(absfile, starts,
                    rotation=15)

    fig, ax = plt.subplots()
    maze.plot(ax)
    plt.show()
