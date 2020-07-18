# gen
from collections import defaultdict, deque
# math
import numpy as np
#graph 
import networkx as nx

class PathGraph(object):
    """ the class creates a path graph where each node represents a path.
    The edges betweens nodes exist if the paths are adjacent.
    the weight of each edge is the length of the 
    """
    def __init__(self,  subPaths, baseGraph):
        self.subPaths = subPaths
        self.baseGraph = baseGraph
        self.pathGraph = nx.DiGraph()
        self.buildGraph()

    def buildGraph(self):
        # build the pathGraph
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


        #unpack
        baseGraph = self.baseGraph
        for grp, path in enumerate(self.subPaths):
            for i, node in enumerate(path[:-1]):
                nxt = path[i+1] # next node
                if node==nxt:
                    continue
                isShared, adj = self.sharedNode(node, baseGraph)
                if isShared:
                    # check the next node
                    grpAdj = baseGraph.nodes[adj]['subgraph']
                    isShared_nxt, adj_nxt = self.sharedNode(nxt, baseGraph)
                    grpAdj_nxt = baseGraph.nodes[adj]['subgraph']
                    
                    if self.pathGraph.has_edge(grp, grpAdj):
                            #if we have this edge in the meta graph go to next path
                            continue           
                    
                    elif isShared_nxt and grpAdj_nxt == grpAdj:
                        # check for path adjacency
                        adj_path = self.subPaths[grpAdj]
                        isPathAdj, dirFwd, adjIdx = self.pathAdj(adj, adj_nxt, adj_path)
                        if isPathAdj:
                            # done!
                            # add to meta graph
                            adjStep = 1 if dirFwd else -1
                            self.pathGraph.add_edge(grp, grpAdj,
                                               weight=len(self.subPaths[grpAdj]),                                       
                                               fwd=dirFwd,
                                               edgePair= (node, nxt, adj, adj_nxt),
                                               edgePairIdx = (i, i+1, adjIdx, adjIdx+adjStep))  
                            self.pathGraph.add_edge(grpAdj, grp,
                                               weight=len(self.subPaths[grp]),                                       
                                               fwd=dirFwd,
                                               edgePair= (adj, adj_nxt, node, nxt),
                                               edgePairIdx = (adjIdx, adjIdx+adjStep, i, i+1)) 

    def sharedNode(self, n, baseGraph): 
        # checks if the node n has a adj node not in the same subGraph 
        grp = baseGraph.nodes[n]['subgraph']
        for adj in baseGraph[n]: # look at all the neighbors
            adjGrp = baseGraph.nodes[adj]['subgraph']
            if adjGrp != grp:
                # if if the subgraph groups are different return True
                return True, adj
        return False, None

    def pathAdj(self, adj, adj_nxt, adj_path):
        for j, p in enumerate(adj_path):
            if p == adj: 
                # check forward along adj path
                if j+1 <len(adj_path) and adj_path[j+1]==adj_nxt:
                    return True, True, j 
                # check reverse along path
                elif j-1 > 0 and adj_path[j-1]==adj_nxt:
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
                adj.sort(key= lambda x: nodeQueue[x], reverse=True)
                adj.sort(key= lambda x: x in self.pathGraph['e'])
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
                        path=['e']
                    else:
                        print('int')
                        path=['i']
                    break

        return metaPaths

    def stitch(self, metaPaths):
        subPaths = self.subPaths
        paths = []
        for mPath in metaPaths:
            path = []
            path += subPaths[mPath[1]] # set path to 1st in the metaPath shallow copy
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

                #get directions
                diff_in = idx_in_nxt-idx_in
                diff_out = idx_out_nxt-idx_out
                
                # get input side merge idx, the lower of the two idx_in's
                mergeIdx = idx_in if diff_in > 0 else idx_in_nxt
                # get output side splice idx, based on the idx_in's
                spliceIdx = idx_out if diff_in > 0 else idx_out_nxt
                # orient and slice the path to be merged 
                if diff_out == diff_in:
                    #reverse path and splice
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




