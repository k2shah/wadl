#gen 
import time
# math
import numpy as np
#graph 
import networkx as nx
#plot
import matplotlib.pyplot as plt
# lib
from wadl.solver.SATproblem import SATproblem
from wadl.graph.multiGraph import MultiGraph
from wadl.graph.pathGraph import PathGraph

class BaseSolver(object):
    """docstring for Solver"""
    def __init__(self, maze):
        self.maze = maze
        self.setup()

    def setup(self):
        self.problem=SATproblem(self.maze.graph,
                                self.maze.limit,
                                self.maze.globalStarts)

    def plot(self, ax):
        self.maze.plot(ax, showGrid=True)

    def solve(self):
        #solve the problem
        return self.problem.solve()



class LinkSolver(object):
    """docstring for LinkSolver"""

    def __init__(self, maze):
        self.maze = maze
        self.setup()

    def setup(self):
        self.mGraph = MultiGraph(self.maze.graph)
        self.problems = []
        for graph in self.mGraph:
            limit = len(graph) + 2 #lets try this?
            self.problems.append(SATproblem(graph, limit))

    def plot(self, ax):
        nGraph = len(self.mGraph)
        cols = self.mGraph.getCols()
        for i, graph in enumerate(self.mGraph):
                # print(graph.nodes)
                col = next(cols)
                # print(colors[colIdx])
                self.maze.plotNodes(ax, nodes=graph.nodes, color=col)

    def presolve(self):
        paths = []
        for i, prob in enumerate(self.problems):
            counter = 0
            solved = False
            while not solved:
                try:
                    solved, path, time = prob.solve()
                    paths.append(path[0])
                except RuntimeError as e:
                    print(f"\tproblem {i} failed, inc path limit")
                    prob.limit += 1 
                    prob.make()
                    counter += 1

                if counter > 5:
                    print(f"problem {i} critical infeasible")
                    paths.append([])
                    break
        return paths

    def solve(self):
        startTime = time.time()
        # presolve for the paths
        paths = self.presolve()
        # build the meta graph
        self.pGraph = PathGraph(paths, self.mGraph.baseGraph)
        paths = self.pGraph.link(self.maze.limit)
        # print time
        solTime = time.time()-startTime
        print("solution time: {:2.5f} sec".format(solTime))
        return True, paths, solTime