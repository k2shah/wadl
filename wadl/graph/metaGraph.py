# os
import os
# gen
from collections import defaultdict
from copy import deepcopy
# math
import numpy as np
from math import ceil
# graph
import networkx as nx
# plot
import matplotlib.pyplot as plt
# lib
from wadl.lib.utils import sub2ind
from wadl.lib.maze import Maze


class MetaGraph(object):
    """docstring for MetaGraph"""
    def __init__(self, graph, size=40):
        # baseGraph
        self.baseGraph = graph
        # list of graphs who's union is the baseGraph
        self.subGraphs = self.findSubGraphs(size)
        # graph of the paths
        self.pathGraph = nx.DiGraph()
        # reindex all the nodes and store their subgraph
        self.nodeIndex = dict()

    def getExtends(self, graph):
        xSort = sorted(graph.nodes, key=lambda x: x[0])
        ySort = sorted(graph.nodes, key=lambda x: x[1])

        xBound = (xSort[0][0], xSort[-1][0])
        yBound = (ySort[0][1], ySort[-1][1])

        return xBound, yBound

    def findSubGraphs(self, size):
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

        subNodes = self.mergeSubGraphs(subNodes, node2sub)
        # there has to be a better way to do this
        maxNodes = len(max(subNodes.values(), key=lambda x: len(x)))
        minNodes = len(min(subNodes.values(), key=lambda x: len(x)))

        subGraphs = [self.baseGraph.subgraph(
            nodes) for nodes in subNodes.values()]
        print(f"found {len(subGraphs)} subgraphs with "
              f"{minNodes} to {maxNodes} nodes")

        for gIdx, graph in enumerate(subGraphs):
            for i, node in enumerate(graph.nodes):
                graph.nodes[node]['index'] = i
                self.baseGraph.nodes[node]['subgraph'] = gIdx

        return subGraphs

    def mergeSubGraphs(self, subNodes, node2sub, mergeSize=10, maxSize=60):
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
                        # print(f"Merging subg {i}"
                        #       f" with {len(nodes)} nodes into subgraph {k}")
                        mergedNodes[k] += nodes
                        mergedNodes.pop(i)
                        break
        return mergedNodes

    def buildPathGraph(self, subPaths):
        # build the pathGraph
        # store the subpaths
        self.subpaths = subPaths
        # check if we have the correct number of paths
        if len(self.subPaths) != len(self.subGraphs):
            raise RuntimeError("subPaths do not match subGraphs")
        # initialize the path graph
        # sorted the graph between interior and exterior subgraphs
        for i, path in enumerate(self.subPaths):
            # if any node as less than 4 connections the subgraph is exterior
            if any([len(self.baseGraph[node]) < 4 for node in path]):
                print(f"e: {i}")
                self.pathGraph.add_edge('e', i, weight=len(path))
            else:
                # else, it is interior
                print(f"i: {i}")
                self.pathGraph.add_edge('i', i, weight=len(path))

            self.pathGraph.add_edge('s', i, weight=len(path))

        # unpack
        baseGraph = self.baseGraph
        for grp, path in enumerate(self.subPaths):
            for i, node in enumerate(path[:-1]):
                nxt = path[i+1]  # next node
                if node == nxt:
                    continue
                isShared, adj = self.sharedNode(node, baseGraph)
                if isShared:
                    # check the next node
                    grpAdj = baseGraph.nodes[adj]['subgraph']
                    isShared_nxt, adj_nxt = self.sharedNode(nxt, baseGraph)
                    grpAdj_nxt = baseGraph.nodes[adj]['subgraph']

                    if self.pathGraph.has_edge(grp, grpAdj):
                        # if this edge is already stored go to next path
                        continue

                    elif isShared_nxt and grpAdj_nxt == grpAdj:
                        # check for path adjacency
                        adj_path = self.subPaths[grpAdj]
                        isPathAdj, dirFwd, adjIdx = self.pathAdj(
                            adj, adj_nxt, adj_path)
                        if isPathAdj:
                            # done!
                            # add to meta graph
                            adjStep = 1 if dirFwd else -1
                            self.pathGraph.add_edge(
                                grp, grpAdj,
                                weight=len(self.subPaths[grpAdj]),
                                fwd=dirFwd,
                                edgePair=(node, nxt, adj, adj_nxt),
                                edgePairIdx=(i, i+1, adjIdx, adjIdx+adjStep))
                            self.pathGraph.add_edge(
                                grpAdj, grp,
                                weight=len(self.subPaths[grp]),
                                fwd=dirFwd,
                                edgePair=(adj, adj_nxt, node, nxt),
                                edgePairIdx=(adjIdx, adjIdx+adjStep, i, i+1))

    def sharedNode(self, n, baseGraph):
        # checks if the node n has a adj node not in the same subGraph
        grp = baseGraph.nodes[n]['subgraph']
        for adj in baseGraph[n]:  # look at all the neighbors
            try:
                adjGrp = baseGraph.nodes[adj]['subgraph']
                if adjGrp != grp:
                    # if the subgraph groups are different return True
                    return True, adj
            except KeyError as e:
                print("no subgraph found for node: ", adj)
                print(e)
                continue
        return False, None

    def pathAdj(self, adj, adj_nxt, adj_path):
        for j, p in enumerate(adj_path):
            if p == adj:
                # check forward along adj path
                if j+1 < len(adj_path) and adj_path[j+1] == adj_nxt:
                    return True, True, j
                # check reverse along path
                elif j-1 > 0 and adj_path[j-1] == adj_nxt:
                    return True, False, j

        return False, False, None

    def link(self, limit):
        metaPaths = self.merge(limit)
        paths = self.stitch(metaPaths)
        return paths

    def merge(self, limit):
        # finds paths of the pathGraph such that len(path) < limit
        nodeQueue = dict()
        for i, path in enumerate(self.subPaths):
            pathLen = len(path)
            nodeQueue[i] = pathLen
            if limit < pathLen:
                raise RuntimeError("distance limit too short")
        metaPaths = []
        # greedy fill of paths
        path = ['e']
        while len(nodeQueue) > 0:
            n = None
            pathLen = 0
            while pathLen < limit:
                n = path[-1]
                adj = list(filter(lambda x: x in nodeQueue.keys(),
                                  self.pathGraph[n]))
                adj.sort(key=lambda x: nodeQueue[x])
                adj.sort(key=lambda x: x in self.pathGraph['e'], reverse=True)
                newNode = False
                for nxt in adj:
                    cost = nodeQueue[nxt]
                    if pathLen + cost < limit:
                        # add to the path
                        path.append(nxt)
                        pathLen += cost
                        del nodeQueue[nxt]
                        newNode = True
                        break
                if len(nodeQueue) == 0 or not newNode:
                    # print(f"merged {path} length: {pathLen}")
                    metaPaths.append(path)
                    # change to interior nodes when external are exhausted
                    if any([n in nodeQueue.keys() for n in self.pathGraph['e']]):
                        print('ext')
                        path = ['e']
                    else:
                        print('int')
                        path = ['i']
                    break

        return metaPaths

    def stitch(self, metaPaths):
        subPaths = self.subPaths
        paths = []
        for mPath in metaPaths:
            path = []
            # set path to 1st in the metaPath shallow copy
            path += subPaths[mPath[1]]
            for edge in zip(mPath[1:], mPath[2:]):
                # get the data from the pathGraph edge
                edgePair = self.pathGraph.edges[edge]['edgePair']
                edgePairIdx = self.pathGraph.edges[edge]['edgePairIdx']
                fwd = self.pathGraph.edges[edge]['fwd']

                # get the idx of the points to merge
                idx_in = path.index(edgePair[0])
                idx_in_nxt = path.index(edgePair[1])
                idx_out = edgePairIdx[2]
                idx_out_nxt = edgePairIdx[3]

                # get directions
                diff_in = idx_in_nxt-idx_in
                diff_out = idx_out_nxt-idx_out

                # get input side merge idx, the lower of the two idx_in's
                mergeIdx = idx_in if diff_in > 0 else idx_in_nxt
                # get output side splice idx, based on the idx_in's
                spliceIdx = idx_out if diff_in > 0 else idx_out_nxt
                # orient and slice the path to be merged
                if diff_out == diff_in:
                    # reverse path and splice
                    mergePath = subPaths[edge[1]][spliceIdx:0:-1] + \
                        subPaths[edge[1]][-1:spliceIdx:-1]
                else:
                    mergePath = subPaths[edge[1]][spliceIdx:-1] + \
                        subPaths[edge[1]][0:spliceIdx]

                # merge at mergeIdx
                path[mergeIdx+1:mergeIdx+1] = mergePath

            # save the merged path
            paths.append(path)
        return paths

    def getCols(self):
        return iter(plt.cm.rainbow(np.linspace(0, 1, len(self.subGraphs))))


if __name__ == '__main__':
    path = os.path.join(os.path.dirname(__file__), '..', '..', 'tests', 'data')
    file = os.path.join(path, "croz_west")

    absfile = os.path.abspath(file)
    maze = Maze(absfile, rotation=15)
    mGraph = MetaGraph(maze.graph)

    fig, ax = plt.subplots()
    colors = mGraph.getCols()

    for i, graph in enumerate(mGraph.subGraphs):
        # print(graph.nodes)
        col = next(colors)
        # print(colors[colIdx])
        maze.plotNodes(ax, nodes=graph.nodes, color=col)
    plt.show()