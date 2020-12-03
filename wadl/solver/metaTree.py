# gen
from collections import OrderedDict
from queue import SimpleQueue
# math
import numpy as np
# graph
import networkx as nx
# plot
from wadl.solver.metaGraph import MetaGraph
# gis


class Pathtree(MetaGraph):
    # PathTree object

    def __init__(self, graph):
        super(Pathtree, self).__init__(graph)

    def buildTree(self, home):
        # make a tree from the base graph
        self.tree = nx.DiGraph()
        self.makeNodes(home)
        self.makeEdge()
        # CHECK IF GRAPH IS DAG
        assert nx.is_directed_acyclic_graph(self.tree)

    def getUTM(self, pt):
        # gets the UTM of a point
        return self.baseGraph.nodes[pt]["UTM"]

    def makeNodes(self, home):
        # make the initial nodes of the graph
        self.tree.add_node("home", UTM=home[0:2], dist=0, size=0)
        for node, path in enumerate(self.subPaths):
            dist, rotatedPath = self.minHomeDist(self.tree.nodes["home"], path)
            self.tree.add_node(node,
                               UTM=self.getUTM(rotatedPath[0]),
                               dist=dist,
                               size=self.pathLength(rotatedPath))
            self.tree.add_edge("home", node, weight=dist)

    def makeEdge(self):
        for e1, e2 in self.pathGraph.edges:
            if e1 in self.tree and e2 in self.tree:
                if self.tree.nodes[e1]["dist"] < self.tree.nodes[e2]["dist"]:
                    self.tree.add_edge(
                        e1, e2, weight=self.tree.nodes[e1]["size"])

    def minHomeDist(self, home, path):
        # rotates the path to find the smallest home transfer distance
        dist, idx = min([(np.linalg.norm(home["UTM"], self.getUTM(pt)), i)
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
        # build the path tree
        if len(routeSet.home) != 1:
            errMsg = "cant support a multihome maze"
            self.logger.error(errMsg)
            raise RuntimeError(errMsg)
            return None
        self.buildTree(routeSet.home)

        # find groups for each tile
        self.groups = OrderedDict()
        for node in sorted(self.tree.nodes,
                           key=lambda x: self.tree.nodes[x]["dist"],
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
                self.logger.info(f"route idx: {groupIdx}")
                queue.put(node)
                # reset all the objects
                metaTree = nx.DiGraph()
                metaTree.add_edge('home', node)
                # build the first segment
                candiate = self.stitch(metaTree)
                if (route := routeSet.check(candiate)) is not None:
                    # build the 1st section
                    self.logger.info(f"accepted {node}")
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
                        if (newRoute := routeSet.check(candiate)) is not None:
                            # accept the node
                            queue.put(n_adj)
                            self.logger.info(f"accepted {node}")
                            self.groups[n_adj] = groupIdx
                            # save the route
                            route = newRoute
                        else:
                            # remove if didn't work
                            self.logger.info(f"rejected {node}")
                            metaTree.remove_node(n_adj)

                # when done with filling
                groupIdx += 1
                if route is None:
                    errMsg = "critcal errror is path linking"
                    self.logger.error(errMsg)
                    raise RuntimeError(errMsg)
                else:
                    self.logger.info(f"pushing {metaTree.nodes}")
                    routeSet.push(route)
        self.nGroups = groupIdx

    def stitch(self, metaTree):
        # get edges to travel in a DF manner
        # print("edges ", metaTree.edges)
        edgeList = nx.dfs_edges(metaTree)
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
        self.logger.info(f"path {path}")
        for section in path:
            node, start, end = section
            # pick the direction
            step = 1 if start < end else -1
            for idx in range(start, end+step, step):
                # get the world pt
                pt = self.subPaths[node][idx]
                # look up and push the UTM
                waypoints.append(self.baseGraph.nodes[pt]['UTM'])
        return self.steamlinePath(waypoints)

    def plot(self, ax):
        colors = ['k', 'r', 'b', 'g', 'c', 'y', 'm']
        for node in self.tree.nodes:
            cord = self.tree.nodes[node]["UTM"]
            color = colors[self.groups[node] % 6]
            ax.scatter(*cord, color=color)
        for e1, e2 in self.tree.edges:
            if self.groups[e1] == self.groups[e2]:
                line = np.array([self.tree.nodes[e1]["UTM"],
                                 self.tree.nodes[e2]["UTM"]])
                ax.plot(line[:, 0], line[:, 1], color='k', linewidth=1)
