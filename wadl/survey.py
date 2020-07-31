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
    def __init__(self, name, outDir, solver="Base"):
        # get solver
        self.solverType = self.getSolver(solver)
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
        # step [40]: grid size
        # distance [1000]: flight lenght in meters
        # altitude [50]: flying alt (agl) in meters
        # speed [5]: flying speed in meters/sec
        
        self.tasks[file] = Maze(file, **kwargs) 

    def setKeyPoints(self, points):
        # set the keyPoints in the survey
        self.keyPoints = points


    def plotKeyPoints(self, ax):
        for key, val in self.keyPoints.items():
            cord = utm.from_latlon(*val)[0:2]
            ax.scatter(*cord, color='k', s=1)
            ax.annotate(key, xy=cord, xycoords='data')

    def view(self, offset=0):
        fig, ax = plt.subplots()
        self.plotKeyPoints(ax)
        for file, maze in self.tasks.items():
            solver = self.solverType(maze)
            solver.plot(ax)

        # figure formats
        plt.gca().set_aspect('equal', adjustable='box')
        # display 
        plt.show()

    def plan(self, plot=False, offset=0, mSize=40):
        fig, ax = plt.subplots(figsize=(16, 16))     
        for task, maze in self.tasks.items():
            try:
                maze.solve(Solver=self.solverType, offset=offset, mSize=mSize)
                if maze.solved:
                    print(f"writing paths")
                    maze.write(self.outDir)
      
            except RuntimeError as e:
                print(f"failure in task: {maze.name}")
                print(e)
            print(f"task {maze.name} finished")
            #plot task
            self.plotKeyPoints(ax)
            maze.plot(ax)
            plt.draw()
            plt.axis('square')
        if plot:
            plt.axis('square')
            plt.gca().set_aspect('equal', adjustable='box')
            plt.show()
        print(f"done")
        # troll annie a bit
        annie = ["annie", "Annie", "schmidt"]
        if any(isAnnie for a in annie if a in self.outDir):
            print("ANNIE GO PET SCOUT!") 


    def getSolver(self, SolverName):
        if SolverName=="Base":
            return BaseSolver
        elif SolverName=="Link":
            return LinkSolver
        else:
            raise RuntimeError('No Solver selected')
