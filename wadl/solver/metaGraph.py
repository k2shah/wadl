# gen
from collections import defaultdict
import logging
# math
import numpy as np
from math import ceil
# graph
import networkx as nx
# plot
import matplotlib.pyplot as plt


class MetaGraph(object):
    """docstring for MetaGraph"""

    def __init__(self, graph, size=40):
        # logging
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)

        # baseGraph
        self.baseGraph = graph
        # list of graphs who's union is the baseGraph
        self.baseSize = size
        self.subGraphs = self.split()
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

    @staticmethod
    def sub2ind(cord, grid):
        # returns the linear index on the square index
        return cord[0] + grid[0]*cord[1]

    def split(self,):
        """splits a graph into sub segments
        size: aprox number of nodes in each sub graph
        """
        subNodes = self.findSubNodes()
        return self.buildSubGraphs(subNodes)

    def findSubNodes(self):
        size = self.baseSize
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
        for node in self.baseGraph.nodes:
            rNode = (node[0] - xBound[0],
                     node[1] - yBound[0])  # get node reltative to bottom left
            # map square index to linear index
            group = (int(rNode[0]/xStep),  int(rNode[1]/yStep))

            # get the index of the subgraph
            subGraphIdx = self.sub2ind(group, (xBlock, yBlock))
            # print(node, rNode, group, subGraphIdx)
            # add to the list
            subNodes[subGraphIdx].append(node)
        return subNodes

    def indexSubGraph(self, graph, gIdx):
        # saves the subgraph index in the basegraph
        for node in graph:
            self.baseGraph.nodes[node]['subgraph'] = gIdx

    def buildSubGraphs(self, subNodes):
        # build connected subgraphs form each list of subnodes
        subGraphs = []
        gIdx = 0
        for nodes in subNodes.values():
            graph = self.baseGraph.subgraph(nodes)
            if nx.is_connected(graph):
                subGraphs.append(graph)
                self.indexSubGraph(graph, gIdx)
                gIdx += 1
            else:
                self.logger.debug("found a non connected section")
                # find the connected compoents
                for n in nx.connected_components(graph):
                    # get the graph from nodes
                    g = self.baseGraph.subgraph(n)
                    subGraphs.append(g)
                    self.indexSubGraph(g, gIdx)
                    gIdx += 1

        self.logger.debug(f"number of graphs before merge {len(subGraphs)}")
        self.logger.debug(f"gIdx counter at {gIdx}")

        subGraphs = self.mergeSubGraphs(subGraphs)
        self.logger.debug(f"number of graphs after merge {len(subGraphs)}")

        # print number of graphs and range of sizes
        maxGraph = max(subGraphs, key=lambda g: len(g))
        minGraph = min(subGraphs, key=lambda g: len(g))
        self.logger.debug("merging done")
        self.logger.info(f"found {len(subGraphs)} subGraphs with "
                         f"{len(minGraph)} to {len(maxGraph)} nodes")

        # merge small subgraphs

        # save local index in subgraph
        for gIdx, graph in enumerate(subGraphs):
            self.indexSubGraph(graph, gIdx)
            for i, node in enumerate(graph.nodes):
                graph.nodes[node]['index'] = i

        return subGraphs

    def mergeSubGraphs(self, subGraphs, minSize=20, maxSize=50):
        # merge small subGraphs into the most connected subGraph
        # if tie pick the smallest subgraph
        merged = dict()
        toMerge = dict()
        nNodes = 0
        for gIdx, graph in enumerate(subGraphs):
            # keep a running total of the nodes
            nNodes += len(graph)
            # check if the graph is small
            if len(graph) > minSize:
                merged[gIdx] = graph
            else:
                toMerge[gIdx] = graph

        self.logger.debug(f"toMerge keys {list(toMerge)}")
        self.logger.debug(f"merged keys{list(merged)}")

        while len(toMerge) > 0:
            sizeOut = sum([len(g) for g in merged.values()])
            sizeIn = sum([len(g) for g in toMerge.values()])
            self.logger.debug(f"toMerge keys {list(toMerge)}")
            self.logger.debug(f"merged keys{list(merged)}")
            self.logger.debug(f"sizes {sizeIn} + {sizeOut} = {sizeIn+sizeOut}")
            # pop item for processing
            gIdx, graph = toMerge.popitem()
            self.logger.debug(f"mergeing {gIdx} of size {len(graph)}")
            # keep running score of best merge candidant
            mergeScore = defaultdict(int)
            for node in graph:
                # get the node index
                nIdx = self.baseGraph.nodes[node]['subgraph']
                for adj in self.baseGraph.neighbors(node):
                    adjIdx = self.baseGraph.nodes[adj]['subgraph']
                    if adjIdx != nIdx:
                        mergeScore[adjIdx] += 1
            self.logger.debug(f"merge scores for {gIdx}: {mergeScore.items()}")
            # sort candiates and merge into the best one

            for adjIdx in sorted(mergeScore,
                                 key=mergeScore.get,
                                 reverse=True):
                if adjIdx in toMerge:
                    oldNodes = list(toMerge[adjIdx])
                elif adjIdx in merged:
                    oldNodes = list(merged[adjIdx])

                # new size of the merged subgraph
                newSize = len(oldNodes) + len(graph)

                if newSize < maxSize:
                    # merge the ith subgraph into the kth subgraph
                    self.logger.debug(f"merging subg {gIdx} into {adjIdx}")
                    # created merged list of nodes
                    mergedNodes = oldNodes + list(graph.nodes)
                    # make new subgeraph and reindex
                    mergedGraph = self.baseGraph.subgraph(mergedNodes)
                    self.indexSubGraph(mergedGraph, adjIdx)

                    # check where to put new subgraph
                    if adjIdx in toMerge and newSize < minSize:
                        toMerge[adjIdx] = mergedGraph
                        self.logger.debug(f"updating small graph {adjIdx}")
                    else:
                        if adjIdx in merged:
                            self.logger.debug(f"updating graph {adjIdx}")
                        else:
                            self.logger.debug(f"new graph {adjIdx}")
                            toMerge.pop(adjIdx)

                        merged[adjIdx] = mergedGraph
                    oldSize = len(oldNodes)
                    self.logger.debug(f"{adjIdx}: {oldSize}=>{newSize}")
                    mergeScore = None
                    break
            if mergeScore is not None:
                self.logger.debug(f"graph {gIdx} could not be merged")
                merged[gIdx] = graph

        # check if the number of nodes is the same
        mergedGraphs = []
        nMergedNodes = 0
        # sort so the colours are pretty
        for key in sorted(merged.keys()):
            graph = merged[key]
            nMergedNodes += len(graph)
            mergedGraphs.append(graph)

        if nNodes != nMergedNodes:
            self.logger.error(f"nodes mismatch {nNodes} vs {nMergedNodes}")
            raise RuntimeError("nodes mismatch")

        return mergedGraphs

    def buildPathGraph(self, subPaths):
        # build the pathGraph
        # store the subpaths
        self.subPaths = subPaths
        # check if we have the correct number of paths
        if len(self.subPaths) != len(self.subGraphs):
            raise RuntimeError("subPaths do not match subGraphs")
        # initialize the path graph
        # sorted the graph between interior and exterior subgraphs
        for i, path in enumerate(self.subPaths):
            # if any node has less than 4 connections the subgraph is exterior
            if any([len(self.baseGraph[node]) < 4 for node in path]):
                # print(f"e: {i}")
                self.pathGraph.add_edge('e', i, weight=len(path))
            else:
                # else, it is interior
                # print(f"i: {i}")
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
                                edgePair=(node, nxt, adj, adj_nxt),
                                edgePairIdx=(i, i+1, adjIdx, adjIdx+adjStep))
                            self.pathGraph.add_edge(
                                grpAdj, grp,
                                weight=len(self.subPaths[grp]),
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
                self.logger.warning("no subgraph found for node: ", adj)
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

    def link(self, routeSet):
        # make a Queue of the of the subgraphs by index
        self.metaPaths = []
        nodeQueue = dict()
        for i, path in enumerate(self.subPaths):
            pathLen = len(path)
            nodeQueue[i] = pathLen

        # greedy fill of paths
        metaPath = ['e']
        while len(nodeQueue) > 0:
            n = metaPath[-1]
            adj = list(filter(lambda x: x in nodeQueue.keys(),
                              self.pathGraph[n]))
            adj.sort(key=lambda x: nodeQueue[x])
            adj.sort(key=lambda x: x in self.pathGraph['e'], reverse=True)
            newNode = False
            for nxt in adj:
                candiatePath = self.stitch(metaPath+[nxt])
                candiateRoute = [self.baseGraph.nodes[node]['UTM']
                                 for node in candiatePath]
                # convert path to route
                if (route := routeSet.check(candiateRoute)) is not None:
                    # add to the path
                    lastRoute = route
                    metaPath.append(nxt)
                    del nodeQueue[nxt]
                    newNode = True
                    break
            if len(nodeQueue) == 0 or not newNode:
                try:
                    routeSet.push(lastRoute)
                    self.metaPaths.append(metaPath)
                    del lastRoute
                except UnboundLocalError:
                    self.logger.error("limit too short-decrease subgraph size")
                    raise RuntimeError("path limit too short")
                # change to interior nodes when external are exhausted
                if any([n in nodeQueue.keys()
                        for n in self.pathGraph['e']]):
                    # print('ext')
                    metaPath = ['e']
                else:
                    # print('int')
                    metaPath = ['i']

    def stitch(self, metaPath):
        subPaths = self.subPaths
        # set path to 1st in the metaPath
        path = []  # force a copy
        path += subPaths[metaPath[1]]
        for edge in zip(metaPath[1:], metaPath[2:]):
            # get the data from the pathGraph edge
            edgePair = self.pathGraph.edges[edge]['edgePair']
            edgePairIdx = self.pathGraph.edges[edge]['edgePairIdx']

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

        # return the merged path
        path = self.steamlinePath(path)
        return path

    @staticmethod
    def steamlinePath(path):
        # removes points in seq that are straight line
        p = [path[0]]
        # get init heading
        h = (path[0][0]-path[0][0],
             path[0][1]-path[0][1])
        for c, n in zip(path[1:], path[2:]):
            # c current pt
            # n next pt
            # get next heading
            nh = (n[0]-c[0], n[1]-c[1])
            if nh != h:
                # if the direction changes, add the pt
                p.append(c)
            h = nh  # save heading
        # add last point
        p.append(path[-1])
        # removes sequentially duplicate points
        return [n for i, n in enumerate(p) if i == 0 or n != p[i-1]]

    def getCols(self):
        return iter(plt.cm.rainbow(np.linspace(0, 1, len(self.subGraphs))))
