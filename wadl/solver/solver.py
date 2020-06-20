#graph 
import networkx as nx
# lib
from wadl.solver.SATproblem import SATproblem
from wadl.graph.multiGraph import MultiGraph

class BaseSolver(object):
    """docstring for Solver"""
    def __init__(self, maze):
        self.maze = maze
        self.setup()

    def setup(self):
        self.problem=SATproblem(self.maze.graph,
                                self.maze.limit,
                                self.maze.globalStarts)

    def solve(self):
        #solve the problem
        return self.problem.solve()



class LinkSolver(BaseSolver):
    """docstring for LinkSolver"""

    def __init__(self, maze):
        super(LinkSolver, self).__init__(maze)

    def setup(self):
        self.mGraph = MultiGraph(self.maze.graph)
        self.problems = []
        for graph in self.mGraph:
            limit = len(graph) + 1 #lets try this?
            self.problems.append(SATproblem(graph, limit))



    def solve(self):
        solTime = 0.0
        paths = []
        for i, prob in enumerate(self.problems):
            counter = 0
            solved = False
            while not solved:
                try:
                    solved, path, time = prob.solve()
                    paths.append(path[0])
                    solTime += time
                except RuntimeError as e:
                    print(f"problem {i} failed, inc path limit")
                    prob.limit += 1 
                    prob.make()
                    counter += 1

                if counter > 5:
                    print(f"problem {i} critial failure")
                    paths.append([])
                    break



        return True, paths, solTime