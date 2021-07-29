#!bin/bash/python3
from pathlib import Path
# deep copying
import numpy as np
import random
import logging
# plot
import matplotlib.pyplot as plt
# gis
import utm
# lib
from wadl.lib.route import RouteSet
from wadl.lib.maze import Maze
from wadl.solver.solver import LinkSolver
from wadl.mission import Mission


class Survey(object):
    """Holds all the information of a single survey

    Args:
        name (str, optional): name of the survey
        outDir (str, optional): location of output directory

    """

    def __init__(self, name="survey", outDir=None):
        # get solver
        self.solvers = dict()
        #self.solver = LinkSolver()
        # save the name of the survey
        self.name = name
        # make the output directory
        self.outDir = Path(name) if outDir is None else Path(outDir/name)
        self.outDir.mkdir(parents=True, exist_ok=True)
        # setup logger
        self.setupLogger()
        # tasks is a dict that maps file name to survey parameters
        self.tasks = dict()
        # key points to display on the
        self.keyPoints = dict()
        self.logger.info("WADL Survey Planner")

    def setupLogger(self):
        # create logger
        rootLogger = logging.getLogger()

        # clean up old loggers
        rootLogger.propagate = False
        if (rootLogger.hasHandlers()):
            rootLogger.handlers.clear()
        # set the new ones
        rootLogger.setLevel(logging.INFO)
        # create file handler which logs even debug messages
        fh = logging.FileHandler(self.outDir/'wadl.log', 'w+')
        fh.setLevel(logging.DEBUG)
        # create console handler with a higher log level
        ch = logging.StreamHandler()
        ch.setLevel(logging.INFO)
        # create formatter and add it to the handlers
        formatter = logging.Formatter(
                     '%(asctime)s| %(name)-25s |%(levelname)8s| %(message)s')
        fh.setFormatter(formatter)
        # add the handlers to the logger
        rootLogger.addHandler(fh)
        rootLogger.addHandler(ch)

        # local logger
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)

    def addTask(self, file, **kwargs):
        """Add a task to the survey.

        Args:
            file (str): filename of geofence
            step (int, optional): grid step size. defaults 40.
            rotation (int, optional): rotation of the grid by radians.
            limit (float, optional): default flight time limit
            home (srt, optional): key(s) of home location(s)
            priority (wadl.lib.Areas): Areas object of high priority sections
            routeParamters (RouteParameters): Desired settings
                for each route in this task

        """
        try:
            if isinstance(kwargs["home"], list):
                kwargs["home"] = [self.keyPoints[h] for h in kwargs["home"]]
            elif isinstance(kwargs["home"], str):
                homeKey = kwargs["home"]
                kwargs["home"] = [self.keyPoints[homeKey]]
        except KeyError:
            self.logger.warning('home not found')
            kwargs["home"] = None

        self.tasks[file] = Maze(file, **kwargs)
        # add to solvers
        self.solvers[self.tasks[file]] = LinkSolver()

    def __getitem__(self, idx):
        key = [*self.tasks][idx]
        return self.tasks[key]

    def __iter__(self):
        return iter(self.tasks.values())

    def at(self, sliced):
        return self.__getitem__(sliced)

    # where is this used?
    def setSolver(self, solver):
        self.solver = solver

    def setSolverParamters(self, parameters):
        """Set the solver parameters.

        Args:
            parameters (SolverParamters): sets the solver settings

        """
        for task, maze in self.tasks.items():
            self.solvers[maze].parameters = parameters
        #self.solver.parameters = parameters

    def setKeyPoints(self, points):
        """Set the keyPoints in the survey.

        Args:
            points (dict): map of str->(lat, long) of key points in the survey.
                These points can be used as home locations.

        """
        self.keyPoints = points

    def plotKeyPoints(self, ax):
        for key, val in self.keyPoints.items():
            cord = utm.from_latlon(*val)[0:2]
            ax.scatter(*cord, color='k', s=1)
            ax.annotate(key, xy=cord, xycoords='data')

    def view(self, showGrid=True, save=None):
        """ View the current survey (unplanned)

        Args:
            showGrid (bool): shows the grid lines of the coverage area
                default True.

        """
        fig, ax = plt.subplots(figsize=(16, 16))
        self.plotKeyPoints(ax)
        for file, maze in self.tasks.items():
            self.solver.setup(maze.graph)
            cols = self.solver.metaGraph.getSubgraphColors()
            maze.plot(ax, showGrid=showGrid, showRoutes=False)
            for i, graph in enumerate(self.solver.metaGraph.subGraphs):
                # print(graph.nodes)
                col = next(cols)
                # print(colors[colIdx])
                maze.plotNodes(ax, nodes=graph.nodes, color=col)
                maze.plotEdges(ax, edges=graph.edges, color=col)

        # figure formats
        plt.gca().set_aspect('equal', adjustable='box')
        # display
        if save is not None:
            plt.savefig(save, bbox_inches='tight', dpi=100)
        else:
            plt.show()

    def plan(self, write=True, showPlot=False, relinking=False):
        """ Plan the survey.

        Args:
            write (bool): write the paths as csv file and save the plot of
                the route. default True
            showPlot (bool): show the plot of the routes. default False.
        """
        # create dict mapping maze to solver
        for task, maze in self.tasks.items():

            #self.solver.setup(maze.graph)
            self.solvers[maze].setup(maze.graph)
            
            try: # issue: maze is changed in setup
                solTime = self.solvers[maze].solve(routeSet=maze.routeSet)
                #solTime = self.solver.solve(routeSet=maze.routeSet)
                maze.solTime = solTime
                # store copy of paths
                maze.calcRouteStats()
                if write:
                    maze.write(self.outDir)

            except RuntimeError as e:
                self.logger.error(f"failure in task: {maze.name}")
                print(e)
                print("\n")
            self.logger.info(f"task {maze.name} finished")
        self.logger.info("done planning")

        # plot
        self.plot(showPlot)
        # call shutdowns
        if (not relinking):
            self.close()

    def relink(self, routeParameters, write=True, showPlot=False):
        # reset route parameters and relink subPaths
        for task, maze in self.tasks.items():
            curSolver = self.solvers[maze]
            #curSolver.metaGraph = copy.deepcopy(curSolver.metaGraphCopy) # dont need?

            maze.routeSet.routeParameters = routeParameters

            try:
                curSolver.mergeTiles(curSolver.subPaths, maze.routeSet)
                maze.calcRouteStats()
                if write:
                    maze.write(self.outDir)
            except RuntimeError as e:
                self.logger.error(f"failure in task: {maze.name}")
                print(e)
                print("\n")
            self.logger.info(f"task {maze.name} finished")
        self.logger.info("done planning")

        # plot
        self.plot(showPlot)
        # call shutdowns and free stuff
        self.close()

    
    def partialComplete(self, completePct):
        # randomly remove last portion of each path to simulate partial completion
        for file, maze in self.tasks.items():
            for i, route in enumerate(maze.routeSet.routes):
                x = random.random()
                # if k == 2 or k == 8 or k == 0 or k==4:
                #     x = .8
                # else:
                #     x = .1
                # of routes will complete
                if x > completePct:
                    print("broken: ", i)
                    # completes random proportion of route
                    y = random.randint(0, len(route.UTMcords))
                    #y = 25
                    route.lastNode = y
                    route.uncompleted = route.UTMcords[y:]
                    # link start to end (generate cycle) and reverse
                    print(len(route.uncompleted))
                    route.uncompleted.append(route.uncompleted[0])
                    route.uncompleted.reverse()
                    route.UTMcords = route.UTMcords[:y]

    def recomplete(self):
        # list with cords for new routes
        # randomly remove last portion of each path to simulate partial completion
        print("recomplete")
        for file, maze in self.tasks.items():
            new_routes = []
            # preserve only routes that are uncompleted
            maze.routeSet.routes = list(filter(lambda x: x.uncompleted is not None, maze.routeSet.routes))
            lost_groups=[]
            linked = []
            # for each route, go through all the nodes, check what connects to them, try to merge route
            for i in maze.routeSet.routes:
                if i.group in linked:
                    continue

                lost_groups.append(i.group)
                linkable = []

                # remember prev attributes
                uncompleted = i.uncompleted

                #find the closest point to home
                i.UTM2GPS(i.UTMZone)
                (dist, idx) = min([(i.DistGPS(np.array(i.home), np.array(pt)), idx)
                         for idx, pt in enumerate(i.GPScords)])
                i.UTMcords = uncompleted[idx:] + uncompleted[1:idx+1]

                # find all nodes in group
                route_subnodes = list(filter(lambda x: self.solvers[maze].metaGraph.groups[x] == i.group, self.solvers[maze].metaGraph.tree.nodes))
                for node in route_subnodes:
                    # check neighbors if in another lost group
                    for adj in self.solvers[maze].metaGraph.tree.neighbors(node):
                        if self.solvers[maze].metaGraph.groups[adj] in lost_groups and self.solvers[maze].metaGraph.groups[adj] != i.group:
                            linkable.append(self.solvers[maze].metaGraph.groups[adj])

                _, new = maze.routeSet.check(i.UTMcords)

                for j in maze.routeSet.routes:
                    if j.group in linkable:
                        print("attempting to link: ")
                        print(i.group, " ", j.group)

                        # link at closest point (hacky)
                        cur_min = 99999999999
                        i_idx=0
                        j_idx=0
                        for idx2, pt1 in enumerate(j.GPScords):
                            (dist, idx1) = min([(i.DistGPS(np.array(pt2), np.array(pt1)), idx)
                                for idx, pt2 in enumerate(i.GPScords)])
                            if dist < cur_min:
                                cur_min = dist
                                i_idx=idx1
                                j_idx=idx2

                        linked = i.UTMcords[:i_idx] + j.UTMcords[:j_idx] + i.UTMcords[i_idx:] + j.UTMcords[j_idx:]

                        passed, candidate = maze.routeSet.check(linked)
                        if passed:
                            i.UTMcords = linked
                            new = candidate
                            linked.append(j.group)
                        print(passed)

                new.group = i.group
                new_routes.append(new)

            maze.routeSet.routes = []
            for route in new_routes:
                if route.group not in linked:
                    maze.routeSet.push(route)





    def plot(self, showPlot=True):
        # plot task
        fig, ax = plt.subplots(figsize=(16, 16))
        for task, maze in self.tasks.items():
            maze.plot(ax)
        self.plotKeyPoints(ax)
        plt.axis('square')
        plt.gca().set_aspect('equal', adjustable='box')
        filename = self.outDir / "routes.png"
        plt.savefig(filename, bbox_inches='tight', dpi=100)
        if showPlot:
            plt.show()
        else:
            plt.close()

    def close(self):
        # release the loggers
        logging.shutdown()
        # close plots
        plt.close()

    def mission(self, missionParams):
        # make a mission.json file
        mission = Mission(missionParams)
        mission.fromSurvey(self)
        mission.write()
