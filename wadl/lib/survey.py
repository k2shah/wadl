#!bin/bash/python3
# import warnings as warn
import os
import csv
import glob
# import sys
# import time
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
from wadl.lib.maze import Maze
from wadl.solver.solver import BaseSolver, LinkSolver

class Survey(object):
    """docstring for Survey
    top level object for a survey
    this objects holds all the information of a single survey """
    def __init__(self, name, outDir):
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
        # keyword arguments for the start locations, step size, and distance limit
        # start = [(0,0), (1,1)]
        # step = 40
        # limit = 20

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
        for task, maze in self.tasks.items():
            maze.plot(ax, showGrid=True)

        # figure formats
        plt.gca().set_aspect('equal', adjustable='box')

        # display 
        plt.show()

    def plan(self, plot=True, Solver="Base"):
        # get solver
        solver = self.getSolver(Solver)

        fig, ax = plt.subplots(figsize=(16, 9))
        self.plotKeyPoints(ax)
        plt.gca().set_aspect('equal', adjustable='box')
        plt.draw()
        
        for task, maze in self.tasks.items():
            try:
                maze.solve(Solver=solver)
                if maze.solved:
                    print(f"generating paths for task {maze.name}")
                    maze.write(self.outDir)
               
            except RuntimeError as e:
                print(f"task {maze.name} failed")

            #plot task
            maze.plot(ax)
            plt.draw()
            plt.pause(.001)
        if plot:
            plt.show()


    def getSolver(self, SolverName):
        if SolverName=="Base":
            return BaseSolver
        elif SolverName=="Link":
            return LinkSolver
