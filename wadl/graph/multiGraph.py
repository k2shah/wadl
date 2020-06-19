# os
import os
# math
import numpy as np
from math import floor, ceil
#graph 
import networkx as nx
# plot
import matplotlib.pyplot as plt
# lib
from wadl.lib.utils import *
from wadl.lib.maze import Maze


class MultiGraph(object):
    """docstring for MultiGraph"""
    def __init__(self, graph):
        self.baseGraph = graph
        self.subgraphs = self.splitGraph_square()



    def splitGraph_square(self, size=40):
        """splits a graph into sub segments
        size: aprox number of nodes in each sub graph
        """
        self.subGraphs = []
        self.metaGraph = nx.Graph () # metaGraph of the subGraphs

        # get bounding box extends on graph
        xBound, yBound = self.getExtends(self.baseGraph)
        # print(self.baseGraph.nodes)
        # print(xBound, yBound)

        #get deltas
        xDelta = xBound[-1] - xBound[0] +1 
        yDelta = yBound[-1] - yBound[0] +1 # +1 for inclusive
        
        # find number of subGraphs
        nNode = xDelta * yDelta 
        nSubGraph = int(nNode/size)
        # print(nSubGraph)

        # print('delta', xDelta, yDelta)
        ar = yDelta/xDelta # aspect raito of graph
        # print('ar', ar)

        # calculate how many blocks on each axis, trying to be as square as posible 
        xBlock = (nSubGraph/ar) **.5
        yBlock = ar*xBlock
        # round up
        xBlock = int(xBlock) +1
        yBlock = int(yBlock) +1
        # print(xBlock, yBlock)

        # get steps on each
        xStep = ceil(xDelta/xBlock)
        yStep = ceil(yDelta/yBlock)

        subNodes = [[] for _ in range(xBlock * yBlock)]
        for node in self.baseGraph.nodes:
            rNode = (node[0] - xBound[0],
                     node[1] - yBound[0] ) # get node reltative to bottom left
            group = (int(rNode[0]/xStep),  int(rNode[1]/yStep)) # map square index to linear index

            # get the index of the subgraph
            subGraphIdx = sub2ind(group, (xBlock, yBlock))
            # print(node, rNode, group, subGraphIdx)
            # add to the list
            subNodes[subGraphIdx].append(node)

        subgraphs = [self.baseGraph.subgraph(nodes) for nodes in subNodes if nodes]
        print(f"Found {len(subgraphs)} subgraps with max block size of {xStep * yStep}")

        return subgraphs





    def getExtends(self, graph):
        xSort = sorted(graph.nodes, key= lambda x :x[0])
        ySort = sorted(graph.nodes, key= lambda x :x[1])

        xBound = (xSort[0][0], xSort[-1][0])
        yBound = (ySort[0][1], ySort[-1][1])

        return xBound, yBound

if __name__ == '__main__':
    starts = [(0,0),
              (1,1)]

    path = os.path.join(os.path.dirname( __file__ ), '..', '..', 'tests', 'data')
    file = os.path.join(path, "croz_west")
    
    absfile = os.path.abspath(file)
    maze = Maze(absfile, starts, rotation=15)
    mGraph = MultiGraph(maze.graph)

    fig, ax = plt.subplots()
    colors = ('r', 'g', 'b', 'm', 'c', 'y', 'k')

    for i, graph in enumerate(mGraph.subgraphs):
            # print(graph.nodes)
            colIdx = i % len(colors) 
            # print(colors[colIdx])
            maze.plotNodes(ax, nodes=graph.nodes, color=colors[colIdx])
    plt.show()