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

            routeSetPrev = maze.routeSet
            maze.routeSet = RouteSet(routeSetPrev.home, routeSetPrev.zone, routeParameters)
            maze.routeSet.data=routeSetPrev.data
            # maze.routeSet.routeParameters = routeParameters
            # maze.routeSet.routes=[]

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

    def stop(self, index, broken=-1):
        # stops each route at index
        # accepts an argument broken for a route that is discontinued at index
        newRoutes=[]
        for file, maze in self.tasks.items():
            solver = self.solvers[maze]
            #print("subpaths: ", solver.metaGraph.subPaths)
            for i, route in enumerate(maze.routeSet.routes):
                route.setMaze(maze)
                if len(route.UTMcords) > index:
                    if i==broken:
                        #index is different
                        route.unstreamlineRoute(solver.metaGraph)
                        route.uncompleted = route.UTMcords[index:]
                        route.prev=route.UTMcords[:index]
                        route.UTMcords=route.prev
                    else:
                        route.unfinished = route.UTMcords[index:]                 
                    #route.UTMcords = route.UTMcords[:index]
                    #newRoutes.append(route)
                else:
                    route.unfinished=[route.UTMcords[-1]]
                newRoutes.append(route)
            maze.routeSet.routes=newRoutes



    def partialComplete(self, completePct):
        # accepts completePct, a percentage of routes that are desired to complete
        # randomly remove last portion of each path to simulate partial completion
        for file, maze in self.tasks.items():
            solver = self.solvers[maze]
            #print("subpaths: ", solver.metaGraph.subPaths)
            for i, route in enumerate(maze.routeSet.routes):
                route.setMaze(maze)
                x = random.random()
                # of routes will complete
                if x > completePct:
                    # completes random portion of route
                    y = random.randint(2, len(route.UTMcords)-2)
                    route.unstreamline(solver.metaGraph,y-1)
                    route.uncompleted = route.UTMcords[y:]
                    # link start to end (generate cycle) and reverse
                    route.uncompleted.reverse()
                    route.UTMcords = route.UTMcords[:y]

    def uncomplete(self, uncompleted):
        # accepts uncompleted, a dictionary mapping uncompleted routes to pts of malfunction
        # randomly remove last portion of each path to simulate partial completion
        for file, maze in self.tasks.items():
            solver = self.solvers[maze]
            #print("subpaths: ", solver.metaGraph.subPaths)
            for i, route in enumerate(maze.routeSet.routes):
                route.setMaze(maze)
                # of routes will complete
                if i in uncompleted:
                    # completes only portion of route
                    y = uncompleted[i]
                    route.unstreamline(solver.metaGraph,y-1)
                    route.uncompleted = route.UTMcords[y:]
                    # link start to end (generate cycle) and reverse
                    route.uncompleted.reverse()
                    route.UTMcords = route.UTMcords[:y]
                    
    def recompleteOnline(self):
        for file, maze in self.tasks.items():
            lost=None
            maze.routeSet.routes = list(filter(lambda x: x.UTMcords is not None, maze.routeSet.routes))
            solver = self.solvers[maze]
            for route in maze.routeSet.routes:
                route.setMaze(maze)
                if route.uncompleted != None:
                    lost = route
                    lost.UTMcords=lost.uncompleted
                    lost.UTM2GPS(route.UTMZone)
                elif route.UTMcords != None:
                    route.prev=route.UTMcords
                    route.UTMcords = route.unfinished
            
            solver.metaGraph.setMaze(maze)
            if lost != None:
                solver.metaGraph.reroute(maze.routeSet, lost)

    def recompleteBFS(self):
        # repartition uncompleted routes to build new routes
        # generate new path tree
        print("recomplete")
        for file, maze in self.tasks.items():
            maze.routeSet.routes = list(filter(lambda x: x.uncompleted is not None, maze.routeSet.routes))
            for route in maze.routeSet.routes:
                route.UTMcords = route.uncompleted
            initial = len(maze.routeSet.routes)
            # remake the path tree
            solver = self.solvers[maze]
            solver.metaGraph.setMaze(maze)
            solver.metaGraph.rebuildTree(maze.routeSet)
            solver.metaGraph.repartition(maze.routeSet)
        return len(maze.routeSet.routes), initial

    def fullSweep(self):
        for task, maze in self.tasks.items():
            curSolver = self.solvers[maze]
            metaGraph = curSolver.metaGraph
            routeSet = maze.routeSet
            for route in routeSet.routes:
                # route.UTMcords = [route.UTMcords[0]]

                route.setMaze(maze)
                route.unstreamlineRoute(metaGraph)

                newRoute = []

                while (len(route.UTMcords) != 0):
                    newRoute += self.sweep(metaGraph, maze, route, newRoute)
                
                route.UTMcords = newRoute
                route.UTM2GPS(route.UTMZone)
       
    
    def sweep(self, metaGraph, maze, route, cur):
        # convert to gridpts
        gridPts = []
        for pt in route.UTMcords:
            gridPts.append(maze.UTM2Grid[(int(pt[0]),int(pt[1]))])
        # check which side is empty

        # go to closest corner
        xBot = min([(pt[0]) for pt in gridPts])
        xTop = max([(pt[0]) for pt in gridPts])
        yBot = min([(pt[1]) for pt in gridPts if pt[0]==xBot])
        yTop = max([(pt[1]) for pt in gridPts if pt[0]==xBot])
        yCorners = [yTop, yBot]

        up=True

        if len(cur) == 0:
            yStart = min([(pt[1]) for pt in gridPts if pt[0]==xBot])
            # also intelligently choose which direction to sweep
        else:
            # print(cur[-1])
            # print(pt)
            # print("yc: ",yCorners)
            cGrid = maze.UTM2Grid[(int(cur[-1][0]),int(cur[-1][1]))]
            _, yStart = min([(abs(cGrid[1] - pt1), pt1)
                         for pt1 in yCorners])
            if yStart == yTop:
                up=False

        startPt = (xBot,yStart)
        print(startPt)


        # go to top
        newRoute = [metaGraph.getUTM(startPt)]
        curPt = startPt
                
        while True:
            # try to go up
            if up:
                above = max([(pt[1]) for pt in gridPts if pt[0]==curPt[0]])
                if above != curPt[1]:
                    curPt = (curPt[0], above)
                    newRoute.append(metaGraph.getUTM(curPt))
                else:
                    break
                # print("above", curPt)
                # go right
                right = (curPt[0]+1, curPt[1])
                if right in gridPts: 
                    curPt = (right[0], max([(pt[1]) for pt in gridPts if pt[0]==right[0]]))
                    newRoute.append(metaGraph.getUTM(curPt))
                else:
                    break
                # print("right", curPt)
                up=True
            # try to go up
            below = min([(pt[1]) for pt in gridPts if pt[0]==curPt[0]])
            if below != curPt[1]:
                curPt = (curPt[0], below)
                newRoute.append(metaGraph.getUTM(curPt))
            else:
                break
            # print("below", curPt)
            # go right
            right = (curPt[0]+1, curPt[1])
            if right in gridPts: 
                curPt = (right[0], min([(pt[1]) for pt in gridPts if pt[0]==right[0]]))

                newRoute.append(metaGraph.getUTM(curPt))
            else:
                break
            # print("right", curPt)
        
        prev=route.UTMcords
        route.UTMcords = newRoute
        route.unstreamlineRoute(metaGraph)
        newGridPts=[]    
        for pt in route.UTMcords:
            newGridPts.append(maze.UTM2Grid[(int(pt[0]),int(pt[1]))])
        remaining = []
        for pt in gridPts:
            if pt not in newGridPts:
                remaining.append(pt)
        route.UTMcords = [metaGraph.getUTM(pt) for pt in remaining]
        return newRoute
        # for pt in newGridPts:
        #     if pt not in gridPts:
        #         print("broke", pt)
        #         route.UTMcords=prev
                        




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
