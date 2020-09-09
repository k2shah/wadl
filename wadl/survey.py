#!bin/bash/python3
# import warnings as warn
# import os
# import csv
# import glob
# import sys
# import time
# plot
import matplotlib.pyplot as plt
# gis
import utm
# lib
from wadl.lib.maze import Maze
from wadl.solver.solver import LinkSolver


class Survey(object):
    """docstring for Survey
    top level object for a survey
    this objects holds all the information of a single survey """

    def __init__(self, name, outDir,
                 solverParam={}, solverType=LinkSolver):
        # get solver
        self.solver = solverType(**solverParam)
        # save the name of the survey
        self.name = name
        # save the output directory
        self.outDir = outDir
        # tasks is a dict that maps file name to survey parameters
        self.tasks = dict()
        # key points to display on the
        self.keyPoints = dict()
        # max number of boolean variables to solve for
        # lower for less powerful machines
        self.varMax = 1.5e4

    def addTask(self, file, **kwargs):
        # add a task to the survey
        # expects a file name
        # keyword arguments:
        # step [40]: grid size
        # limit [1000]: flight time limit in seconds
        # home [None]: key of the home location
        try:
            homeKey = kwargs["home"]
            kwargs["home"] = self.keyPoints[homeKey]
        except KeyError:
            print('home not found')
            kwargs["home"] = None

        self.tasks[file] = Maze(file, **kwargs)

    def setKeyPoints(self, points):
        # set the keyPoints in the survey
        self.keyPoints = points

    def plotKeyPoints(self, ax):
        for key, val in self.keyPoints.items():
            cord = utm.from_latlon(*val)[0:2]
            ax.scatter(*cord, color='k', s=1)
            ax.annotate(key, xy=cord, xycoords='data')

    def view(self):
        fig, ax = plt.subplots()
        self.plotKeyPoints(ax)
        for file, maze in self.tasks.items():
            self.solver.setup(maze.graph)
            cols = self.solver.metaGraph.getCols()
            maze.plot(ax)
            for i, graph in enumerate(self.solver.metaGraph.subGraphs):
                # print(graph.nodes)
                col = next(cols)
                # print(colors[colIdx])
                maze.plotNodes(ax, nodes=graph.nodes, color=col)
                maze.plotEdges(ax, edges=graph.edges, color=col)

        # figure formats
        plt.gca().set_aspect('equal', adjustable='box')
        # display
        plt.draw()

    def plan(self, plot=True):
        for task, maze in self.tasks.items():
            self.solver.setup(maze.graph)
            try:
                solTime = self.solver.solve(routeSet=maze.routeSet)
                maze.solTime = solTime
                maze.write(self.outDir)

            except RuntimeError as e:
                print(f"\tfailure in task: {maze.name}")
                print(e)
            print(f"\ttask {maze.name} finished")
        print("done planning")

        # plot result
        if plot:
            self.plot()

    def plot(self):
        # plot task
        fig, ax = plt.subplots(figsize=(16, 16))
        for task, maze in self.tasks.items():
            self.plotKeyPoints(ax)
            maze.plot(ax)
            plt.draw()
            plt.axis('square')
            plt.gca().set_aspect('equal', adjustable='box')
            plt.draw()
