# os
import os
# gen
from collections import defaultdict
from copy import deepcopy
# math
import numpy as np
from math import floor, ceil
# graph
import networkx as nx
# plot
import matplotlib.pyplot as plt
# lib
from wadl.lib.utils import *


class MultiGraph(object):
    """docstring for MultiGraph"""

    def __init__(self, graph, size=40):
        self.baseGraph = graph
        self.subGraphs = self.splitGraph(size)
        # reindex all the nodes and store their subgraph
        self.nodeIndex = dict()
        for gIdx, graph in enumerate(self.subGraphs):
            for i, node in enumerate(graph.nodes):
                graph.nodes[node]['index'] = i
                self.baseGraph.nodes[node]['subgraph'] = gIdx

    def getExtends(self, graph):
        xSort = sorted(graph.nodes, key=lambda x: x[0])
        ySort = sorted(graph.nodes, key=lambda x: x[1])

        xBound = (xSort[0][0], xSort[-1][0])
        yBound = (ySort[0][1], ySort[-1][1])

        return xBound, yBound

    def splitGraph(self, size):
        """splits a graph into sub segments
        size: aprox number of nodes in each sub graph
        """
        self.subGraphs = []

        # get bounding box extends on graph
        xBound, yBound = self.getExtends(self.baseGraph)
        # print(self.baseGraph.nodes)
        # print(xBound, yBound)

        # get deltas
        xDelta = xBound[-1] - xBound[0] + 1
        yDelta = yBound[-1] - yBound[0] + 1  # +1 for inclusive

        # find number of subGraphs
        nNode = xDelta * yDelta
        nSubGraph = int(nNode/size)
        # print(nSubGraph)

        # print('delta', xDelta, yDelta)
        ar = yDelta/xDelta  # aspect raito of graph
        # print('ar', ar)

        # calculate how many blocks on each axis, be as square as posible
        xBlock = (nSubGraph/ar) ** .5
        yBlock = ar*xBlock
        # round up
        xBlock = int(xBlock) + 1
        yBlock = int(yBlock) + 1
        # print(xBlock, yBlock)

        # get steps on each
        xStep = ceil(xDelta/xBlock)
        yStep = ceil(yDelta/yBlock)

        subNodes = defaultdict(list)
        node2sub = dict()  # map from node to it's subgraph
        for node in self.baseGraph.nodes:
            rNode = (node[0] - xBound[0],
                     node[1] - yBound[0])  # get node reltative to bottom left
            # map square index to linear index
            group = (int(rNode[0]/xStep),  int(rNode[1]/yStep))

            # get the index of the subgraph
            subGraphIdx = sub2ind(group, (xBlock, yBlock))
            # print(node, rNode, group, subGraphIdx)
            # add to the list
            subNodes[subGraphIdx].append(node)
            node2sub[node] = subGraphIdx

        subNodes = self.mergeSubgraphs(subNodes, node2sub)
        # there has to be a better way to do this
        maxNodes = len(max(subNodes.values(), key=lambda x: len(x)))
        minNodes = len(min(subNodes.values(), key=lambda x: len(x)))

        subGraphs = [self.baseGraph.subgraph(
            nodes) for nodes in subNodes.values()]
        print(f"found {len(subGraphs)} subgraphs with"
              f"{minNodes} to {maxNodes} nodes")

        return subGraphs

    def mergeSubgraphs(self, subNodes, node2sub, mergeSize=10, maxSize=60):
        # merge into the subgraph with the most conections
        # if tie pick the smallest suubgraph
        mergedNodes = deepcopy(subNodes)
        for i, nodes in subNodes.items():
            if len(nodes) < mergeSize:
                # keep running score of best merge candidant
                mergeScore = defaultdict(int)
                for node in nodes:
                    for adj in self.baseGraph.neighbors(node):
                        adjIdx = node2sub[adj]
                        if adjIdx != i:
                            mergeScore[adjIdx] += 1
                # sort candiates and merge into the best one
                # print(i, nodes, mergeScore)
                for k in sorted(mergeScore, key=mergeScore.get, reverse=True):
                    if len(mergedNodes[k]) + len(nodes) < maxSize:
                        # merge the ith subgraph into the kth subgraph
                        # print(f"Merging subgraph {i} with {len(nodes)} nodes into subgraph {k}")
                        mergedNodes[k] += nodes
                        mergedNodes.pop(i)
                        break
        return mergedNodes

    def getCols(self):
        return iter(plt.cm.rainbow(np.linspace(0, 1, len(self))))

    def __iter__(self):
        return iter(self.subGraphs)

    def __len__(self):
        return len(self.subGraphs)


if __name__ == '__main__':
    starts = [(0, 0),
              (1, 1)]

    path = os.path.join(os.path.dirname(__file__), '..', '..', 'tests', 'data')
    file = os.path.join(path, "croz_west")

    absfile = os.path.abspath(file)
    maze = Maze(absfile, starts, rotation=15)
    mGraph = MultiGraph(maze.graph)

    fig, ax = plt.subplots()
    colors = ('r', 'g', 'b', 'm', 'c', 'y', 'k')

    for i, graph in enumerate(mGraph):
            # print(graph.nodes)
        colIdx = i % len(colors)
        # print(colors[colIdx])
        maze.plotNodes(ax, nodes=graph.nodes, color=colors[colIdx])
    plt.show()
