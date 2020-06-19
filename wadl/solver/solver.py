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
from wadl.solvers.SATproblem import SATproblem

class BaseSolver(object):
    """docstring for Solver"""
    def __init__(self, maze):
        self.maze = maze
        self.setup()

    def setup(self):
        raise NotImplementedError

    def solve(self):
        '''
        if solution is found return 
        return True, self.output() 
        else
        return False, None
        '''
        raise NotImplementedError


