#!/usr/bin/python3
import warnings as warn
import os
import sys
import time
# math
import numpy as np
import numpy.linalg as la
import numpy.random as rand
#graph 
import networkx as nx
# plot
import matplotlib.pyplot as plt
# lib
from wadl.lib.utils import *
from wadl.solver.solver import SATSolver
# solver
import z3
z3.set_param('parallel.enable', True)
# z3.set_param('verbose', 1)

class LinkSolver(SATSolver):
    """docstring for LinkSolver"""

    def __init__(self, maze):
        super(LinkSolver, self).__init__(maze)

    def setup(self):
        print(self.maze.graph)


    def solve(self):
        raise NotImplementedError

