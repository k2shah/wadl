#graph 
import networkx as nx
# lib
from wadl.solver.SATproblem import SATproblem

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


    def solve(self):
        raise NotImplementedError
