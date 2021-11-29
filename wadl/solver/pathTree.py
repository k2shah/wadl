# gen
from collections import OrderedDict
from queue import SimpleQueue
# math
import numpy as np
# nest for loop
from itertools import product
# graph
import networkx as nx
# plot
from wadl.solver.metaGraph import MetaGraph
# gis
import utm
# plot
import matplotlib.pyplot as plt
import copy


class PathTree(MetaGraph):
    # PathTree object

    def __init__(self, graph, **kwargs):
        super(PathTree, self).__init__(graph, **kwargs)

    def buildTree(self, routeSet):
        # make a tree from the base graph
        self.tree = nx.DiGraph()
        self.makeNodes(routeSet)
        self.makeEdges()
        # CHECK IF GRAPH IS DAG
        try:
            assert nx.is_directed_acyclic_graph(self.tree)
        except AssertionError:
            errMsg = "graph is not DAG"
            self.logger.error(errMsg)
            raise RuntimeError(errMsg)

    def rebuildTree(self, routeSet):
        # rebuilding tree for offline replanning
        # make a tree from the base graph
        self.tree = nx.DiGraph()
        self.remakeNodes(routeSet)
        self.remakeEdges()
        # CHECK IF GRAPH IS DAG
        try:
            assert nx.is_directed_acyclic_graph(self.tree)
        except AssertionError:
            errMsg = "graph is not DAG"
            self.logger.error(errMsg)
            raise RuntimeError(errMsg)

    def getUTM(self, pt):
        # gets the UTM of a point
        return self.baseGraph.nodes[pt]["UTM"]

    def setMaze(self, maze):
        self.maze=maze

    # create a node for every subPath, link to "home"
    def makeNodes(self, routeSet):
        # make the initial nodes of the graph
        utmHome = [utm.from_latlon(*home)[0:2] for home in routeSet.home]
        self.tree.add_node("home", UTM=utmHome, homeDist=0)
        for tile, path in enumerate(self.subPaths):
            UTMpath = [self.getUTM(pt) for pt in self.steamlinePath(path)]
            _, route = routeSet.check(UTMpath[:-1])
            # unpack route metrics into the node
            self.tree.add_node(tile,
                               UTM=self.getUTM(path[0]),
                               homeDist=route.len_tran,
                               homeTime=route.ToF_tran,
                               survDist=route.len_surv,
                               survTime=route.ToF_surv
                               )
            self.tree.add_edge("home", tile)

    def remakeNodes(self, routeSet):
        # remaking nodes for offline replanning
        # make the initial nodes of the graph
        utmHome = [utm.from_latlon(*home)[0:2] for home in routeSet.home]
        self.tree.add_node("home", UTM=utmHome, homeDist=0)
        #create tile for every lost path
        for tile, path in enumerate(routeSet.routes):
            # unpack route metrics into the node
            self.tree.add_node(tile,
                               UTM=path.UTMcords,
                               homeDist=path.len_tran,
                               homeTime=path.ToF_tran,
                               survDist=path.len_surv,
                               survTime=path.ToF_surv
                               )
            self.tree.add_edge("home", tile)

    def makeEdges(self):
        for e1, e2 in self.pathGraph.edges:
            if e1 in self.tree and e2 in self.tree:
                #edge between adjacent nodes if first one in edge list is closer to home dist
                if self.tree.nodes[e1]["homeDist"] < self.tree.nodes[e2]["homeDist"]:
                    self.tree.add_edge(e1, e2)

    def remakeEdges(self):
        # reamke nodes for offline replanning
        for n1 in self.tree.nodes:
            for n2 in self.tree.nodes:
                #edge between adjacent nodes if first one in edge list is closer to home dist
                if n1=="home" or n2=="home":
                    continue
                if self.tree.nodes[n1]["homeDist"] < self.tree.nodes[n2]["homeDist"]:
                    self.tree.add_edge(n1, n2)

    def minHomeDist(self, home, path):
        # rotates the path to find the smallest home transfer distance
        dist, idx = min([(np.linalg.norm(home["UTM"] - self.getUTM(pt)), i)
                         for i, pt in enumerate(path)])
        return dist, path[idx:] + path[1:idx+1]

    def pathLength(self, path):
        # calculates length in m of the path
        length = 0
        for pt0, pt1 in zip(path, path[1:]):
            utm0 = self.getUTM(pt0)
            utm1 = self.getUTM(pt1)
            length += np.linalg.norm(utm1-utm0)
        return length

    def link(self, routeSet):
        # build the tree and partition it
        self.buildTree(routeSet)
        self.nGroups = self.partition(routeSet)

    def partition(self, routeSet):
        # find groups for each tile
        self.edgeGroups = []
        self.groups = OrderedDict()
        for node in sorted(self.tree.nodes,
                           key=lambda x: self.tree.nodes[x]["homeDist"],
                           reverse=True):
            self.groups[node] = 0
        groupIdx = 1
        for node in self.groups:
            if node == 'home':
                continue
            group = self.groups[node]
            if group == 0:
                # start building a new group
                queue = SimpleQueue()
                self.groups[node] = groupIdx
                self.logger.debug(f"route idx: {groupIdx}")
                queue.put(node)
                # reset all the objects
                metaTree = nx.Graph()
                metaTree.add_edge('home', node)
                # build the first segment
                candiate, edgeList = self.stitch(metaTree)
                passed, route = routeSet.check(candiate)
                if passed:
                    # build the 1st section
                    self.logger.debug(f"accepted {node}")
                else:
                    raise RuntimeError("path limit too short")
                # fill the route
                while not queue.empty():
                    n = queue.get()
                    # predecessors of node
                    inEdges = sorted(self.tree.in_edges(n), key=self.inScore)
                    #inEdges = sorted(self.tree.in_edges(n), key=lambda x: x[0])
                    for n_adj, _ in inEdges:
                        if n_adj == 'home' or self.groups[n_adj] != 0:
                            continue
                        # test the new route
                        # subNodes of the route are in the metaTree for this iteration
                        metaTree.add_edge(n, n_adj)
                        candiate, edgeList = self.stitch(metaTree)
                        passed, newRoute = routeSet.check(candiate)
                        if passed:
                            # accept the node
                            queue.put(n_adj)
                            self.logger.debug(f"accepted {node}")
                            self.groups[n_adj] = groupIdx
                            # save the route
                            route = newRoute
                        else:
                            # remove if didn't work
                            self.logger.debug(f"rejected {node}")
                            metaTree.remove_node(n_adj)
                            edgeList = self.updateHomeEdge(metaTree)

                # when done with filling
                route.group = groupIdx
                groupIdx += 1
                if route is None:
                    errMsg = "critcal errror is path linking"
                    self.logger.error(errMsg)
                    raise RuntimeError(errMsg)
                else:
                    self.logger.debug(f"pushing {metaTree.nodes}")
                    self.edgeGroups.append(edgeList)
                    routeSet.push(route)
        nGroups = groupIdx-1
        return nGroups

    def getClosest(self, i, j, route):
        # accept two complete lists of GPS cords i, j and a route object
        # return the closest pair of points in  i, j
        
        (dist, i_idx, j_idx) = min([(route.DistGPS(np.array(p1), np.array(p2)), i1, i2)
            for (i1, p1), (i2, p2) in product(enumerate(i),enumerate(j))])

        return i_idx, j_idx, dist

    def getClosestDist(self,i,j,route):
        # returns the closest distance between points in a pair of lists i, j
        _,_, dist = self.getClosest(i,j,route)
        return dist

    def closestHome(self, r):
        # reorders path for route r so that first point is closest to home
        r.UTM2GPS(r.UTMZone)
        (dist, idx) = min([(r.DistGPS(np.array(r.home), np.array(pt)), idx)
            for idx, pt in enumerate(r.GPScords)])

        lenPrev = len(r.UTMcords)
        r.unstreamline(self,idx-1)
        idx+=len(r.UTMcords)-lenPrev
        r.UTMcords = r.UTMcords[idx:] + r.UTMcords[:idx]

    def mergePts(self, i, i_idx):
        # prepare route object i to be streamlined at index i_idx
        # return list of mergeable pts
        iPrev=len(i.UTMcords)
        iBack=i_idx-1
        if iBack>=0:
            i.unstreamline(self,i_idx-1)
        else:
            iBack=0
        if i_idx+len(i.UTMcords)-iPrev+1 < len(i.UTMcords)-1:
            i.unstreamline(self,i_idx+len(i.UTMcords)-iPrev+1)

        # find candidate pts for merging
        iVals=range(iBack, i_idx+len(i.UTMcords)-iPrev+2)
        iVals = list(filter(lambda x: x < len(i.UTMcords) and x >= 0, iVals))
     
        i.UTM2GPS(i.UTMZone)

        return iVals


    def mergePaths(self,i,j):
        # accepts a pair of route objects i, j and merges there paths at closest point
        # returns a list of UTM cords
        candiate=[]
        i.UTM2GPS(i.UTMZone)
        j.UTM2GPS(j.UTMZone)
        i_idx, j_idx, _ = self.getClosest(i.GPScords,j.GPScords, i)
 
        #unstreamline closest pts to find closest pairs
        iVals=self.mergePts(i, i_idx)
        jVals=self.mergePts(j, j_idx)
     
        # find closest point
        i_idx=0
        i_idx2=0
        j_idx=0
        j_idx2=0
        if len(iVals)>1 and len(jVals)>1:
            (dist, i_idx, i_idx2, j_idx, j_idx2) = min([(i.DistGPS(np.array(i.GPScords[i1]), np.array(j.GPScords[j1]))+j.DistGPS(np.array(i.GPScords[i2]), np.array(j.GPScords[j2])), i1, i2, j1, j2)
                for i1,i2,j1,j2 in product(iVals,iVals,jVals,jVals) if abs(j1-j2)==1 and abs(i1-i2)==1])
                

        #ensure paths do not cross at merging
        if i_idx<i_idx2:
            if j_idx2 > j_idx:
                prev=len(j.UTMcords)
                j.UTMcords.reverse()
                j_idx=len(j.UTMcords)-j_idx-1
                j.unstreamline(self,j_idx-1)
                j_idx+=len(j.UTMcords)-prev
        else:
            if j_idx2 < j_idx:
                prev=len(j.UTMcords)
                j.UTMcords.reverse()
                j_idx=len(j.UTMcords)-j_idx2-1
                j.unstreamline(self,j_idx-1)
                j_idx+=len(j.UTMcords)-prev
        j.UTM2GPS(j.UTMZone)

        # construct candidate path
        i.unstreamline(self,min(i_idx,i_idx2))
        j.unstreamline(self,j_idx-1)
        candiate = i.UTMcords[:min(i_idx,i_idx2)+1] + j.UTMcords[j_idx:] + j.UTMcords[:j_idx] + i.UTMcords[min(i_idx,i_idx2)+1:]

        #streamline path
        waypoints = []
        for pt in candiate:
            waypoints.append(self.maze.UTM2Grid[(int(pt[0]),int(pt[1]))])
        candiate = [self.getUTM(pt) for pt in self.steamlinePath(waypoints)]
        return candiate

    def closestEndPt(self, r, lost):
        # figure out which endpt in lost is closer to r
        # reverse route if last pt is closer

        _, _, dStart = self.getClosest(r.GPScords, [lost.GPScords[0]], r)
        _, _, dEnd = self.getClosest(r.GPScords, [lost.GPScords[len(lost.GPScords)-1]], r)
        if dEnd < dStart:
            lost.UTMcords.reverse()
            lost.UTM2GPS(lost.UTMZone)

    def sortRoutes(self, routeSet, lost):
        candiates = dict()
        unchanged = []
        for route in routeSet.routes:
            if route.uncompleted == None:
                prev1=route
                # should check front and back
                
                #self.closestEndPt(route, lost)
                _, trial = routeSet.check([lost.UTMcords[0]])
                #r_idx, l_idx, _ = self.getClosest(route.GPScords,trial.GPScords, route)
                trial.setMaze(self.maze)
                route.UTM2GPS(route.UTMZone)
                trial.UTM2GPS(trial.UTMZone)
                #check front and back for merging
                r_idx, _, _ = self.getClosest(route.GPScords, trial.GPScords, route)
                route.unstreamline(self, r_idx)
                new = route.UTMcords[:r_idx+1] + trial.UTMcords + route.UTMcords[r_idx+1:]
                #prev cords are just those that have already been completed
                passed, av = routeSet.check(route.prev+new)

                if passed:
                    print(passed)
                    route.UTMcords=route.prev+route.UTMcords
                    route.UTM2GPS(route.UTMZone)
                    candiates[route] = av.ToF - av.limit
                else:
                    route.UTMcords = route.prev+route.UTMcords
                    route.UTM2GPS(route.UTMZone)
                    unchanged.append(route)
        return unchanged, candiates


    def reroute(self, routeSet, lost):
        print("lost", len(lost.UTMcords))
        print("prev", len(lost.prev))
        newRoutes=[]
        unchanged, p_candiates = self.sortRoutes(routeSet, lost)
        print("cands:", len(p_candiates))
        newRoutes=unchanged
        # sort based on dist from start of lost cords
        s_candiates = sorted(p_candiates, key=lambda x: self.getClosestDist([lost.GPScords[0]], x.GPScords, lost))
        candiates=dict()
        for c in s_candiates:
            candiates[c]=p_candiates[c]
        for route in candiates.keys():
            # append if possible
            remaining = abs(candiates[route])
            #print("r", remaining)
            #adjust per route (not const)
            remainingDist = remaining*5
            outDist = remainingDist/2
            print("od", outDist)
            route.UTM2GPS(route.UTMZone)
            self.closestEndPt(route, lost)
            r_idx, l_idx, _ = self.getClosest(route.GPScords,[lost.GPScords[0]], route)

            addPts = []
            ol = lost.UTMcords
            lost.UTM2GPS(lost.UTMZone)
            #print(ol)
            #print(lost.GPScords)
            while outDist > 0:
                print(outDist)
                if len(lost.UTMcords)==0:
                    break
                #lost.unstreamline(self, 0)
                addPts.append(lost.UTMcords[0])
                if len(lost.UTMcords)<2:
                    break
                d = route.DistGPS(np.array(lost.GPScords[0]), np.array(lost.GPScords[1]))
                #print(d)
                #print(lost.GPScords[0],lost.GPScords[1])
                outDist-=d
                lost.UTMcords=lost.UTMcords[1:]
                lost.UTM2GPS(lost.UTMZone)
            route.UTM2GPS(route.UTMZone)

            if len(addPts)!=0:
                print("recovered: ", len(addPts))
                route.unstreamline(self, r_idx)
                route.UTMcords = route.UTMcords[:r_idx+1]+addPts+route.UTMcords[r_idx+1:]
                p, route = routeSet.check(route.UTMcords)
                print(p)
            newRoutes.append(route)


        routeSet.routes=[]
        # lost.UTMcords = ol
        if len(lost.UTMcords)!=0:
            print("needs new route")
            print(len(lost.UTMcords))
            lost.UTMcords=lost.prev
            lost.UTM2GPS(lost.UTMZone)
        else:
            print("full recomplete")
            lost.UTMcords=lost.prev
            lost.UTM2GPS(lost.UTMZone)
        routeSet.push(lost)
        for r in newRoutes:
            routeSet.push(r)


    def repartition(self, routeSet):
        # find groups for each tile
        routes = []
        old = []
        self.oldTotal = len(routeSet.routes)
        self.merges = 0
        for r in routeSet.routes:
            #find the closest point to home
            r.UTM2GPS(r.UTMZone)
            self.closestHome(r)
            old.append(r)

        self.groups = OrderedDict()
        # sort nodes based on dist from closest home pt
        for node in sorted(self.tree.nodes,
                           key=lambda x: self.tree.nodes[x]["homeDist"],
                           reverse=True):
            self.groups[node] = 0
        groupIdx = 1
   
        for node in self.groups:
            if node == 'home':
                continue
            group = self.groups[node]
            if group == 0:
                # start building a new group
                queue = SimpleQueue()
                self.groups[node] = groupIdx
                self.logger.debug(f"route idx: {groupIdx}")
                queue.put(node)
                route = old[node]
                cur_cords = route.UTMcords
                # fill the route
                while not queue.empty():
                    n = queue.get()
                    print("cur node: ", n)
                    # predecessors of node

                    edges = list(filter(lambda x: x[0] != "home",self.tree.in_edges(n)))
                    inEdges = sorted(edges, key=lambda x: self.getClosestDist(routeSet.routes[x[0]].GPScords,routeSet.routes[n].GPScords,routeSet.routes[n]))

                    for n_adj, _ in inEdges:
                        if n_adj == 'home' or self.groups[n_adj] != 0:
                            continue
                        
                        i = routeSet.routes[n]
                        i.UTMcords = cur_cords
                        j = routeSet.routes[n_adj]

                        # merging routes here
                        print("attempting: ", n, n_adj)

                        candiate = self.mergePaths(i,j)

                        passed, newRoute = routeSet.check(candiate)
                        print(passed)

                        if passed:
                            # accept the node
                            self.merges+=1
                            i.UTMcords = candiate
                            j.UTMcords = candiate
                            cur_cords = candiate
                            queue.put(n_adj)
                            self.logger.debug(f"accepted {node}")
                            self.groups[n_adj] = groupIdx
                            # save the route
                            route = newRoute
                        else:
                            # remove if didn't work
                            self.logger.debug(f"rejected {node}")

                # when done with filling
                route.group = groupIdx
                groupIdx += 1
                if route is None:
                    errMsg = "critcal errror is path linking"
                    self.logger.error(errMsg)
                    raise RuntimeError(errMsg)
                else:
                    routes.append(route)
        nGroups = groupIdx-1
        routeSet.routes = []
        for i, r in enumerate(routes):
            r.setMaze(self.maze)
            self.closestHome(r)
            routeSet.push(r)
        self.newTotal = nGroups
        return nGroups

    def inScore(self, edge):
        # returns the in degree of the edge minus the assigned groups
        # essentially returns the number of free nodes into this node
        localEdges = self.tree.edges(edge[0])
        # get initial score
        score = len(localEdges)
        for n0, n1 in localEdges:
            if self.groups[n0] != 0 or self.groups[n1] != 0:
                score -= 1
        return score

    def stitch(self, tree):
        # takes a tree and appends the home to the closest node
        # then builds the complete path from the tree
        # get the close
        # get edges to travel in a DF manner
        edgeList = self.updateHomeEdge(tree)

        # add the first metaNode
        startNode = edgeList[0][1]
        path = [(startNode, 0, len(self.subPaths[startNode])-1)]

        for edge in edgeList:
            if "home" in edge:
                continue
            path = self.insertTile(path, edge[0], edge[1])
        return self.unravelPath(path), edgeList


    def updateHomeEdge(self, tree):
        """checks the home edge on the meta tree and updates it if a new node
        is better """
        tree.remove_node('home')
        bestNode = min(tree.nodes,
                       key=lambda x: self.tree.nodes[x]["homeDist"])
        tree.add_edge('home', bestNode)
        return list(nx.dfs_edges(tree, source='home'))

    def insertTile(self, path, n_in, n_out):
        # adds the n_out tile to the path at n_in tile at the correct spot
        # get size of insert
        insertSize = len(self.subPaths[n_out])
        # get location
        edgePairIdx = self.pathGraph.edges[(
            n_in, n_out)]['edgePairIdx']
        idx_in, idx_in_nxt, idx_out, idx_out_nxt = edgePairIdx
        # find the insert point
        newSection = None
        for i, (node, start, end) in enumerate(path):
            if node == n_in:
                # previous segment is forward
                if start <= idx_in <= end or end <= idx_in_nxt <= start:
                    newSection = self.allginTile((start, end), n_in, n_out,
                                                 edgePairIdx, insertSize)
                    break
        # insert into path matched
        if newSection is not None:
            path[i:i+1] = newSection
        else:
            raise RuntimeError(f"could not match node {n_out}")
        return path

    @staticmethod
    def allginTile(segment, n_in, n_out, edgePairIdx, insertSize):
        # unpack (yes this is messy)
        start, end = segment
        # get direction of previous (in) segment
        isForward = start < end
        # determine the insert alignment
        idx_in, idx_in_nxt, idx_out, idx_out_nxt = edgePairIdx
        diff_in = idx_in < idx_in_nxt
        # determine previous section exit and enter point
        if isForward == diff_in:
            break_in = [idx_in, idx_in_nxt]
            break_out = [idx_out, idx_out_nxt]
        else:
            break_in = [idx_in_nxt, idx_in]
            break_out = [idx_out_nxt, idx_out]
        # determine alignment of sequential (out) (segment)
        diff_out = break_out[0] < break_out[1]
        if diff_out:
            break_end = [0, insertSize-1]
        else:
            break_end = [insertSize-1, 0]

        # build the new section
        newSection = [(n_in, start, break_in[0]),
                      (n_out, break_out[0], break_end[0]),
                      (n_out, break_end[1], break_out[1]),
                      (n_in, break_in[1], end)]
        return newSection

    def unravelPath(self, path):
        waypoints = []
        # unravel each section
        self.logger.debug(f"path {path}")
        for section in path:
            node, start, end = section
            # pick the direction
            step = 1 if start < end else -1
            for idx in range(start, end+step, step):
                # get the world pt
                waypoints.append(self.subPaths[node][idx])
        # stream line the path and convert to UTM
        # x = [self.getUTM(pt) for pt in waypoints]
        # print(x)
        return [self.getUTM(pt) for pt in self.steamlinePath(waypoints)]

    def plot(self, ax):
        colors = list(plt.cm.rainbow(np.linspace(0, 1, len(self.groups))))
        for node in self.tree.nodes:
            if node == "home":
                continue
            cord = self.tree.nodes[node]["UTM"]
            color = colors[self.groups[node]]
            ax.scatter(*cord, color=color)
        for e1, e2 in self.tree.edges:
            if e1 == "home":
                continue
            if self.groups[e1] == self.groups[e2]:
                line = np.array([self.tree.nodes[e1]["UTM"],
                                 self.tree.nodes[e2]["UTM"]])
                ax.plot(line[:, 0], line[:, 1], color='k', linewidth=1)
