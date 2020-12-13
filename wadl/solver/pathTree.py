# gen
from collections import OrderedDict
from queue import SimpleQueue
# math
import numpy as np
import cvxpy as cvx
# graph
import networkx as nx
# plot
from wadl.solver.metaGraph import MetaGraph
# gis
import utm
# plot
import matplotlib.pyplot as plt


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

    def getUTM(self, pt):
        # gets the UTM of a point
        return self.baseGraph.nodes[pt]["UTM"]

    def makeNodes(self, routeSet):
        # make the initial nodes of the graph
        utmHome = [utm.from_latlon(*home)[0:2] for home in routeSet.home]
        self.tree.add_node("home", UTM=utmHome, homeDist=0)
        for node, path in enumerate(self.subPaths):
            UTMpath = [self.getUTM(pt) for pt in self.steamlinePath(path)]
            _, route = routeSet.check(UTMpath)
            # unpack route metrics into the node
            self.tree.add_node(node,
                               UTM=self.getUTM(path[0]),
                               homeDist=route.len_tran,
                               homeTime=route.ToF_tran,
                               survDist=route.len_surv,
                               survTime=route.ToF_surv
                               )
            self.tree.add_edge("home", node)

    def makeEdges(self):
        for e1, e2 in self.pathGraph.edges:
            if e1 in self.tree and e2 in self.tree:
                if self.tree.nodes[e1]["homeDist"] < self.tree.nodes[e2]["homeDist"]:
                    self.tree.add_edge(e1, e2)

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
        self.partition(routeSet)

    def partition(self, routeSet):
        # find groups for each tile
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
                metaTree = nx.DiGraph()
                metaTree.add_edge('home', node)
                # build the first segment
                candiate = self.stitch(metaTree)
                passed, route = routeSet.check(candiate)
                if passed:
                    # build the 1st section
                    self.logger.debug(f"accepted {node}")
                else:
                    raise RuntimeError("path limit too short")
                # fill the route
                while not queue.empty():
                    n = queue.get()
                    for n_adj, _ in self.tree.in_edges(n):
                        if n_adj == 'home' or self.groups[n_adj] != 0:
                            continue
                        # test the new route
                        metaTree.add_edge(n, n_adj)
                        candiate = self.stitch(metaTree)
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

                # when done with filling
                groupIdx += 1
                if route is None:
                    errMsg = "critcal errror is path linking"
                    self.logger.error(errMsg)
                    raise RuntimeError(errMsg)
                else:
                    self.logger.debug(f"pushing {metaTree.nodes}")
                    routeSet.push(route)
        self.nGroups = groupIdx

    def stitch(self, tree):
        # get edges to travel in a DF manner
        # print("edges ", metaTree.edges)
        edgeList = nx.dfs_edges(tree)
        # add the first metaNode
        startNode = next(edgeList)[1]
        path = [(startNode, 0, len(self.subPaths[startNode])-1)]

        for edge in edgeList:
            if edge[0] == "home":
                continue
            path = self.insertTile(path, edge[0], edge[1])
        return self.unravelPath(path)

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
        return [self.getUTM(pt) for pt in self.steamlinePath(waypoints)]

    def plot(self, ax):
        colors = list(plt.cm.rainbow(np.linspace(0, 1, self.nGroups)))
        for node in self.tree.nodes:
            cord = self.tree.nodes[node]["UTM"]
            color = colors[self.groups[node]]
            ax.scatter(*cord, color=color)
        for e1, e2 in self.tree.edges:
            if self.groups[e1] == self.groups[e2]:
                line = np.array([self.tree.nodes[e1]["UTM"],
                                 self.tree.nodes[e2]["UTM"]])
                ax.plot(line[:, 0], line[:, 1], color='k', linewidth=1)


# class PathTreeMilp(PathTree):
#     """class to split the PathTree with a MILP"""

#     def __init__(self, graph, **kwargs):
#         super(PathTreeMilp, self).__init__(graph, **kwargs)

#     def makeMilp(self, nGroups):
#         N = len(self.graph)
#         M = len(self.graph.edges)

#         # node maps
#         node2idx = {n: i for i, n in enumerate(self.graph)}
#         # edge maps
#         edge2idx = dict()
#         for i, m in enumerate(self.graph.edges):
#             # graph is a dag so only need to cache one direction
#             edge2idx[m] = i
#             edge2idx[tuple(reversed(m))] = i

#         k = nGroups
#         # size limit
#         g = self.limit

#         # cvx
#         X = cvx.Variable((N, k), boolean=True)
#         Z = cvx.Variable((M, k), boolean=True)
#         # Y = cvx.Variable((N, k), boolean=True)
#         cost = cvx.sum([c @ X[:, i] for i in range(k)])
#         # cost = cvx.sum([(t.T @ Y[:, i]) for i in range(k)])
#         const = []
#         # is assigned
#         const += [cvx.sum(X, axis=1) == np.ones(N)]
#         const += [cvx.sum(Z, axis=1) <= np.ones(M)]
#         # has start node
#         # const += [cvx.sum(Y, axis=0) == np.ones(k)]
#         # start node is in subgraph
#         # const += [Y <= X]
#         for i in range(k):
#             # under limit
#             const += [c @ X[:, i] <= g]

#             # min 1 edge max 2 edges per node
#             for n, node in enumerate(self.graph.nodes):
#                 const += [X[n, i] <= cvx.sum([Z[edge2idx[e], i]
#                                               for e in self.graph.edges(node)])]
#                 const += [cvx.sum([Z[edge2idx[e], i]
#                                    for e in self.graph.edges(node)]) <= 2]

#             # edge only allowed if node is in grp
#             for m, edge in enumerate(self.graph.edges):
#                 n1 = node2idx[edge[0]]
#                 n2 = node2idx[edge[1]]
#                 const += [Z[m, i] <= (.5)*(X[n1, i] + X[n2, i])]

#             # tree constraint
#             const += [cvx.sum(X[:, i]) == cvx.sum(Z[:, i])+1]

#         # form and solve
#         prob = cvx.Problem(cvx.Minimize(cost), const)
#         return prob

#     def getCosts(self, routeSet):
#         """use the routeSet parameters and the edges to build the edge cost.
#         Use the distance information in edge and speed in the routeSet to
#         calculate the Edge costs as a time
#         """

#         self.limit = routeSet.routeParameters["limit"]
#         transferSpeed = routeSet.routeParameters["xfer_speed"]
#         speed = routeSet.routeParameters["speed"]
#         edgeCosts = dict()
#         for u, v, d in self.graph.edges(data="weight"):
#             if u == "home":
#                 cost = d*transferSpeed + 20  # 30 seconds for ascend/descend
#             else:
#                 cost = d*speed
#             edgeCosts[(u, v)] = cost
#         return edgeCosts

#     def link(self, routeSet):
#         pass
