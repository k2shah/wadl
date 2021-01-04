#!bin/bash/python3
from pathlib import Path
import logging
# plot
import matplotlib.pyplot as plt
# gis
import utm
# lib
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
        self.solver = LinkSolver()
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

    def setSolver(self, solver):
        self.solver = solver

    def setSolverParamters(self, parameters):
        """Set the solver paramters.

        Args:
            parameters (SolverParamters): sets the solver settings

        """
        self.solver.parameters = parameters

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

    def view(self, showGrid=True):
        """ View the current survey (unplanned)

        Args:
            showGrid (bool): shows the grid lines of the coverage area
                default True.

        """
        fig, ax = plt.subplots(figsize=(16, 16))
        self.plotKeyPoints(ax)
        for file, maze in self.tasks.items():
            self.solver.setup(maze.graph)
            cols = self.solver.metaGraph.getCols()
            maze.plot(ax, showGrid=showGrid)
            for i, graph in enumerate(self.solver.metaGraph.subGraphs):
                # print(graph.nodes)
                col = next(cols)
                # print(colors[colIdx])
                maze.plotNodes(ax, nodes=graph.nodes, color=col)
                maze.plotEdges(ax, edges=graph.edges, color=col)

        # figure formats
        plt.gca().set_aspect('equal', adjustable='box')
        # display
        plt.show()

    def plan(self, write=True, showPlot=False):
        """ Plan the survey.

        Args:
            write (bool): write the paths as csv file and save the plot of
                the route. default True
            showPlot (bool): show the plot of the routes. default False.
        """
        for task, maze in self.tasks.items():
            self.solver.setup(maze.graph)
            try:
                solTime = self.solver.solve(routeSet=maze.routeSet)
                maze.solTime = solTime
                if write:
                    maze.write(self.outDir)

            except RuntimeError as e:
                self.logger.error(f"failure in task: {maze.name}")
                print(e)
            self.logger.info(f"task {maze.name} finished")
        self.logger.info("done planning")

        # plot
        self.plot(showPlot)

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

    def mission(self, missionParams):
        # make a mission.json file
        mission = Mission(missionParams)
        mission.fromSurvey(self)
        mission.write()
