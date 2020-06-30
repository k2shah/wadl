# gen
from collections import defaultdict 
# math
import numpy as np
#graph 
import networkx as nx

class PathGraph(object):
    """ the class creats a path graph where each node represents a path.
    The edges betweens nodes exsist if the paths are adjacent.
    the weight of each edge is the lenght of the 
    """
    def __init__(self,  subPaths, baseGraph):
        self.subPaths = subPaths
        self.baseGraph = baseGraph
        self.pathGraph = nx.DiGraph()
        self.buildGraph()

    def buildGraph(self):
        # build the pathGraph
        # initialize the path graph
        for i, path in enumerate(self.subPaths):
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
                            #if we have this edge in the metagraph go to next path
                            continue           
                    
                    elif isShared_nxt and grpAdj_nxt == grpAdj:
                        # check for path adjajency
                        adj_path = self.subPaths[grpAdj]
                        isPathAdj, dirFwd = self.pathAdj(adj, adj_nxt, adj_path)
                        if isPathAdj:
                            # done!
                            # add to metagraph
                            self.pathGraph.add_edge(grp, grpAdj,
                                               weight=len(self.subPaths[grpAdj]),                                       
                                               fwd=dirFwd,
                                               edgePair= (node, nxt, adj, adj_nxt))  
                            self.pathGraph.add_edge(grpAdj, grp,
                                               weight=len(self.subPaths[grp]),                                       
                                               fwd=dirFwd,
                                               edgePair= (adj, adj_nxt, node, nxt))

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
                    return True, True
                # check reverse along path
                elif j-1 > 0 and adj_path[j-1]==adj_nxt:
                    return True, False
                
        return False, False

    def link(self, limit):
        metaPaths = self.merge(limit)
        paths = self.stitch(metaPaths)
        return paths

    def merge(self, limit):
        # finds paths of the pathGraph such that len(path) < limit
        nodeQueue = dict()
        for i, path in enumerate(self.subPaths):
            nodeQueue[i] = len(path) 
        metaPaths = []
        # greedy fill of paths
        while len(nodeQueue) > 0:
            path = ['s']
            n = None
            pathLen = 0
            while pathLen < limit:
                n = path[-1]
                adj = list(filter(lambda x: x in nodeQueue.keys(),
                                  self.pathGraph[n]))
                adj.sort(key= lambda x: nodeQueue[x])
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
                    print(f"paths mereged: {pathLen}")
                    metaPaths.append(path)
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
                fwd = self.pathGraph.edges[edge]['fwd']
                mergePath = subPaths[edge[1]] # get the next path to merge
                print(edgePair, fwd)
                
                # check merge direction 
                if fwd: 
                    # if fwd then the toop loops are || and the second loop needs to be flipped
                    mergePath = list(reversed(mergePath))
                # find merge location 
                mergeIndex_In = path.index(edgePair[0]) 
                mergeIndex_Out = mergePath.index(edgePair[2]) 
               
                # splice and rejoin
                mergePath = mergePath[mergeIndex_Out:-1] + mergePath[0:mergeIndex_Out]
                # merge at index_in
                path[mergeIndex_In+1:mergeIndex_In+1] = mergePath
            # save the merged path
            paths.append(path)
        return paths




