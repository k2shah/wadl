from wadl.solver.pathTree import PathTree
import cvxpy as cvx
from itertools import compress
import numpy as np
import networkx as nx

class PathTreeMilp(PathTree):
    """class to split the PathTree with a MILP"""

    def __init__(self, graph, **kwargs):
        super(PathTreeMilp, self).__init__(graph, **kwargs)

    def runMilp(self, costDict, nGroups):
        # unpack
        N = len(self.tree)
        M = len(self.tree.edges)
        # groups
        k = nGroups
        # size limit
        g = self.limit

        # node maps
        node2idx = {n: i for i, n in enumerate(self.tree)}
        # edge maps
        edge2idx = dict()
        for i, m in enumerate(self.tree.edges):
            # graph is a dag so only need to cache one direction
            edge2idx[m] = i

        # flatten to array
        costs = np.full(len(costDict), np.nan)
        for i, edge in enumerate(edge2idx):
            costs[i] = costDict[edge]
        try:
            assert np.nan not in costs
        except AssertionError:
            raise RuntimeError("found nan in costs, lookup and map failed")

        # cvx
        # node placement
        X = cvx.Variable((N, k), boolean=True)
        # edge placement
        Z = cvx.Variable((M, k), boolean=True)

        # build cost
        c = cvx.sum([costs @ Z[:, i] for i in range(k)])
        q = []
        # is assigned
        q += [cvx.sum(X[1:, :], axis=1) == np.ones(N-1)]
        q += [cvx.sum(Z, axis=1) <= np.ones(M)]
        # has start node
        # const += [cvx.sum(Y, axis=0) == np.ones(k)]
        # start node is in subgraph
        # const += [Y <= X]
        for i in range(k):
            # under limit
            q += [costs @ Z[:, i] <= g]
            # has home node
            q += [X[0, i] == 1]
            # has only one home edge
            q += [cvx.sum([Z[edge2idx[e], i]
                           for e in self.tree.out_edges('home')]) == 1]

            # min 1 edge incoming per node
            for n, node in enumerate(self.tree.nodes):
                if node == "home":
                    continue
                q += [X[n, i] <= cvx.sum([Z[edge2idx[e], i]
                                          for e in self.tree.in_edges(node)])]
#                 q += [cvx.sum([Z[edge2idx[e], i]
#                                    for e in self.tree.edges(node)]) <= 2]

            # edge only allowed if node is in grp
            for m, edge in enumerate(self.tree.edges):
                n1 = node2idx[edge[0]]
                n2 = node2idx[edge[1]]
                q += [2.0*Z[m, i] <= (X[n1, i] + X[n2, i])]

            # tree constraint
            q += [cvx.sum(X[:, i]) == cvx.sum(Z[:, i])+1]

        # form and return
        prob = cvx.Problem(cvx.Minimize(c), q)
        prob.solve(solver=cvx.GUROBI,
                   #                    verbose=True
                   )
        print(f"problem status: {prob.status} with value {prob.value:1.2f}")

        if prob.status == "optimal":
            subEdges = [list(compress(self.tree.edges, Z[:, i].value))
                        for i in range(k)]
            edgeGroups = list(filter(lambda x: len(x) > 0, subEdges))
            # check costs
            for i, group in enumerate(edgeGroups):
                cost = 0
                for edge in group:
                    cost += costDict[edge]
                print(f"{i}: {cost}")

            return prob.status, edgeGroups
        return prob.status, None

    def getCosts(self, routeSet):
        """use the routeSet parameters and the edges to build the edge cost.
        Use the distance information in edge and speed in the routeSet to
        calculate the Edge costs as a time
        """

        self.limit = routeSet.routeParameters["limit"]
        edgeCosts = dict()
        for u, v in self.tree.edges():
            cost = self.tree.nodes[v]['survTime']
            # if it's a transfer route, add the transfer cost into the edge
            if u == "home":
                transferTime = self.tree.nodes[v]['homeTime']
                cost += transferTime + 10  # 10 seconds for buffer

#             print(f"({u}, {v}) -> {cost}")
            edgeCosts[(u, v)] = cost
        return edgeCosts

    def extractPaths(self, groups, routeSet):
        # extracts the paths from the edge list given in the groups container
        for i, edges in enumerate(groups):
            tree = nx.DiGraph()
            tree.add_edges_from(edges)
            path = self.stitch(tree)
            passed, route = routeSet.check(path)
            if passed is False:
                print(f"route{i} failed:\n")
                print(f"len {route.length}, ToF {route.ToF}, wps {len(route.waypoints)}")
            routeSet.push(route)

    def nGroupsEstimate(self, routeSet, costDict):
        # estimate the number of groups needed
        # this is a heuristic
        # get some data
        transferDists = []
        tileLengths = []
        for u, v in self.tree.edges:
            if u == 'home':
                transferDists.append(costDict[(u, v)])
            else:
                tileLengths.append(costDict[(u, v)])
        nTiles_route = (self.limit - np.min(transferDists)) / \
            np.mean(tileLengths)
        return int(len(self.subGraphs)/nTiles_route)

    def partition(self, routeSet):
        costDict = self.getCosts(routeSet)
        nGroups = self.nGroupsEstimate(routeSet, costDict)
        solved = False
        #  guard for some small ones to  make sure there's at least 1 partition
        nGroups = max(1, nGroups-1)
        while not solved:
            print(f"linking with {nGroups} groups")
            status, groups = self.runMilp(costDict, nGroups=nGroups)
            solved = status == "optimal"
            nGroups += 1

        self.extractPaths(groups, routeSet)
        return groups
