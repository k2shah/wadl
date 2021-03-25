# io
from pathlib import Path
import logging
# math
import numpy as np
# graph
import networkx as nx
# plot
import matplotlib.pyplot as plt
# gis
import utm
from shapely.geometry import Polygon, Point, LineString
# lib
from wadl.lib.fence import Fence
from wadl.lib.route import RouteSet


class Maze(Fence):
    """Holds the geofence data, coverage grid, and planned routes

    Attributes:
        graph (networkx.Graph). coverage grid as a graph
        routeSet (RouteSet). set of routes that cover the area inside this Maze

    Args:
        file (str): location of geofence file (csv).
        step (int, optional): grid spacing in (m).
            default 40.
        rotation (float, optional): grid rotation in rads.
            default 0.
        home ([tuple], optional): list of (lat, long) of the desired home(s)
            default none.
        routeParameters (RouteParameters, optional): desired route parameters.

    """

    def __init__(self,
                 file,
                 step=40,
                 rotation=0,
                 home=None,
                 routeParameters=None):
        super(Maze, self).__init__(Path(file))
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)
        self.solved = False
        self.routeStats = None
        # set parameters
        # grid parameters
        self.theta = rotation
        self.step = step
        # build grid graph
        self.buildGrid()
        self.nNode = len(self.graph)
        self.logger.info(f"generated maze with {self.nNode} nodes")
        # UAV path parameters
        self.home = home
        self.nNode = len(self.graph)  # store size of nodes
        self.routeSet = RouteSet(self.home, self.UTMZone, routeParameters)

    def __len__(self):
        # number of nodes
        return len(self.graph)

    # Grid setup
    @staticmethod
    def rot2D(theta):
        # theta is in rads
        c = np.cos(theta)
        s = np.sin(theta)
        return np.array([[c, -s],
                         [s, c]])

    def rotateGrid(self):
        self.R = self.rot2D(np.radians(self.theta))
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

        # check edges
        # remove edges that intersect the boundary
        for n0, n1 in self.graph.edges:
            line = LineString([self.graph.nodes[n0]['UTM'],
                               self.graph.nodes[n1]['UTM']])

            if self.poly.boundary.intersects(line):
                self.graph.remove_edge(n0, n1)

        # save the index of each node
        for i, node in enumerate(self.graph):
            self.graph.nodes[node]['index'] = i

    def calcRouteStats(self):
        # log route data
        self.logger.info(f"\tgenerated {len(self.routeSet)} routes")
        surveyTofs = 0
        transferTofs = 0
        for i, route in enumerate(self.routeSet):
            self.logger.info(f"{i}: {route.length:.2f}m \t{route.ToF:.2f}s")
            surveyTofs += route.ToF_surv
            transferTofs += route.ToF_tran
        totalTime = surveyTofs + transferTofs 
        ratio = surveyTofs/transferTofs
        self.stats = dict()
        lengths = [route.length for route in self.routeSet]
        # find the number of steps
        nStep = self.routeSet.data['nSteps']
        eff = self.nNode/nStep
        self.stats["path efficiency"] = eff
        totalEff = (eff*surveyTofs)/totalTime
        self.stats["total efficiency"] = totalEff
        self.stats["total time"] = totalTime
        # stats
        self.stats["mean"] = np.mean(lengths)
        self.stats["std"] = np.std(lengths)
        self.stats["ToF_ratio"] = ratio
        # generate output
        self.statsString = f"mean:\t{self.stats['mean']:.2f}m"
        self.statsString += f"\nstd:\t{self.stats['std']:.2f}m"
        self.statsString += f"\nused {nStep} steps for a {self.nNode} graph"
        self.statsString += f"\npath efficiency:\t{eff*100:2.2f}%"
        self.statsString += f"\ntotal efficiency:\t{totalEff*100:2.2f}%"
        self.statsString += f"\nToF ratio: \t{ratio:.3f}"
        self.statsString += f"\ntotal ToF: \t{totalTime:.3f}s"
        self.logger.info(self.statsString)
        return self.statsString

    def calcDistMatrix(self, cutoff=2):
        # L1 distance
        soft_inf = 1000000000
        D = np.ones(shape=(self.nNode, self.nNode))*soft_inf
        for i, ni in enumerate(self.graph):
            for j, nj in enumerate(self.graph):
                l1 = (abs(ni[0] - nj[0]) + abs(ni[1]-nj[1]))
                if l1 > cutoff:
                    D[i, j] = soft_inf
                else:
                    D[i, j] = l1*self.step
        return D

    def export_ORTools(self, cutoff=1, num_vehicles=None):
        data = {}
        limit = self.routeSet.routeParameters["limit"]
        speed = self.routeSet.routeParameters["speed"]
        xferSpeed = self.routeSet.routeParameters["xfer_speed"]
        # distance matrix
        D = self.calcDistMatrix(cutoff=cutoff)
        D = D/speed
        # expand the distance matrix withe home point
        homeDists = []
        nHome = len(self.home)
        data['UTM'] = {node: self.graph.nodes[node]['UTM']
                       for node in self.graph}

        # SAVE home utms as ind -> utm
        data['homeUTM'] = {}
        for i, pt in enumerate(self.home):
            pt_utm = np.array(utm.from_latlon(*pt)[0:2])
            data['homeUTM'][self.nNode+i] = pt_utm
            distances = [np.linalg.norm(self.graph.nodes[node]['UTM']-pt_utm)
                         for node in self.graph]
            homeDists.append(distances)
        homeDists = np.array(homeDists)/xferSpeed
        # block arrangement
        homeBlock = 10000*(np.ones((nHome, nHome))-np.eye(nHome))
        D = np.block([[D, homeDists.T],
                      [homeDists, homeBlock]])

        data["distance_matrix"] = D.astype(int)
        data["ind2node"] = list(self.graph.nodes)
        # estimate number of agents
        maxDist = limit * speed
        if num_vehicles is None:
            num_vehicles = int((self.nNode*self.step)/maxDist)+1
        data['num_vehicles'] = num_vehicles
        # [START starts_ends]
        data['starts'] = [self.nNode + (i % nHome)
                          for i in range(num_vehicles)]
        data['ends'] = data['starts']
        data['maxDist'] = int(maxDist)
        data['maxTime'] = int(limit)
        data['nNode'] = self.nNode
        data['nHome'] = nHome
        data['UTMZone'] = self.UTMZone

        return data

    # write

    def write(self, filePath):
        """Write the maze information to a file

        Args:
            filePath (str): file path for output location.

        """

        nRoute = len(self.routeSet)
        self.taskName = self.name + f'_s{self.step}_r{nRoute}'
        taskDir = filePath / self.taskName
        taskDir.mkdir(exist_ok=True)  # make dir if not exists
        # write maze configuration information
        self.writeInfo(taskDir)
        # write paths as GPS csv files.
        pathDir = taskDir / "routes"
        pathDir.mkdir(exist_ok=True)  # make dir if not exists
        self.writeRoutes(pathDir)
        # save the figure
        fig, ax = plt.subplots(figsize=(16, 16))
        self.plot(ax)
        plt.axis('square')
        plotName = taskDir / "routes.png"
        plt.savefig(plotName, bbox_inches='tight', dpi=100)
        plt.close(fig)

    def writeInfo(self, filePath):
        # writes the Maze information of the test
        outFile = filePath / "info.txt"
        with outFile.open('w') as f:

            f.write('\nGrid size\n')
            f.write(str(self.nNode))

            f.write('\nSolution time (sec)\n')
            f.write(str(self.solTime))

            if self.statsString is None:
                self.calcRouteStats()
            f.write('\nRoute Statistics\n')
            f.write(self.statsString)

    def writeRoutes(self, pathDir):
        self.routeSet.write(pathDir)

    def writeGrid(self, outFile, UTM=True):
        """writes the grid to file

        Args:
            outFile (str): name of output file

        """
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
                       color=color, s=5)

    def plotEdges(self, ax, color='k', edges=None):
        # plot edges
        if edges is None:
            edges = self.graph.edges

        for e1, e2 in edges:
            line = np.array([self.graph.nodes[e1]["UTM"],
                             self.graph.nodes[e2]["UTM"]])
            ax.plot(line[:, 0], line[:, 1],
                    color=color, linewidth=1)

    def plotRoutes(self, ax):
        cols = iter(plt.cm.rainbow(np.linspace(0, 1, len(self.routeSet))))
        for route in self.routeSet:
            route.plot(ax, color=next(cols))

    def plot(self, ax, showGrid=False, showRoutes=True):
        """plot the geofence with grid overlay

        Args:
            ax (pyplot.axis): axis object from pyplot you want to draw on
            showGrid (bool, optional): show the grid.
                default False.
            showRoutes (bool, optional): show the routes
                default True.
        """

        # plot fence
        super(Maze, self).plot(ax)

        # plot maze
        if showGrid:
            # self.plotNodes(ax)
            self.plotEdges(ax)
        if showRoutes:
            self.plotRoutes(ax)
