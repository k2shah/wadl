#!bin/bash/python3
from pathlib import Path
import logging
# plot
import matplotlib.pyplot as plt
# gis
import utm
# lib
from .lib.maze import Maze
from .solver.solver import LinkSolver
from .mission import Mission


class Survey(object):
    """docstring for Survey
    top level object for a survey
    this objects holds all the information of a single survey """

    def __init__(self, name="survey", outDir=None):
        # get solver
        self.solver = LinkSolver()
        # save the name of the survey
        self.name = name
        # make the output directory
        self.outDir = Path(name) if outDir is None else Path(outDir)
        self.outDir.mkdir(exist_ok=True)
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
        # add a task to the survey
        # expects a file name
        # keyword arguments:
        # step [40]: grid size
        # limit [1000]: flight time limit in seconds
        # home [None]: key(s) of the home location(s)
        try:
            if isinstance(kwargs["home"], tuple):
                kwargs["home"] = tuple(self.keyPoints[h]
                                       for h in kwargs["home"])
            elif isinstance(kwargs["home"], str):
                homeKey = kwargs["home"]
                kwargs["home"] = self.keyPoints[homeKey]
        except KeyError:
            self.logger.warning('home not found')
            kwargs["home"] = None

        self.tasks[file] = Maze(file, **kwargs)

    def setSolver(self, solver):
        self.solver = solver

    def setSolverParamters(self, parameters):
        self.solver.parameters = parameters

    def setKeyPoints(self, points):
        # set the keyPoints in the survey
        self.keyPoints = points

    def plotKeyPoints(self, ax):
        for key, val in self.keyPoints.items():
            cord = utm.from_latlon(*val)[0:2]
            ax.scatter(*cord, color='k', s=1)
            ax.annotate(key, xy=cord, xycoords='data')

    def view(self, showGrid=True):
        fig, ax = plt.subplots()
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

    def plan(self, plot=True, write=False):
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

    def plot(self, save=True):
        # plot task
        fig, ax = plt.subplots(figsize=(16, 16))
        for task, maze in self.tasks.items():
            self.plotKeyPoints(ax)
            maze.plot(ax)
            plt.axis('square')
            plt.gca().set_aspect('equal', adjustable='box')
            filename = self.outDir / "routes.png"
            plt.savefig(filename, bbox_inches='tight', dpi=100)
            plt.show()

    def mission(self, missionParams):
        # make a mission.json file
        mission = Mission(missionParams)
        mission.fromSurvey(self)
        mission.write()
