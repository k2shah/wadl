import numpy as np
#graph 
import networkx as nx
# plot
import matplotlib.pyplot as plt
# lib
from wadl.lib.maze import Maze


class MultiGraph(object):
    """docstring for MultiGraph"""
    def __init__(self, graph):
        self.baseGraph = graph
        
    def splitGraph(self, size=40):
        """splits a graph into sub segments
        size: max number of nodes in each sub graph