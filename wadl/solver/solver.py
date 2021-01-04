# gen
import time
import logging
# lib
from wadl.solver.SATproblem import SATproblem
from wadl.solver.metaGraph import MetaGraph
from wadl.lib.parameters import Parameters
from tqdm import tqdm


class SolverParameters(Parameters):
    """docstring for """

    def __init__(self, default=True):
        super(SolverParameters, self).__init__(default)

    def setDefaults(self):
        self["subGraph_size"] = 40
        self["SATBound_offset"] = 2
        self["timeout"] = 60
        self["maxProblems"] = 10


class BaseSolver(object):
    """docstring for Solver"""

    def __init__(self, parameters=None):
        # logging
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)

        # param
        self.parameters = parameters
        if parameters is None:
            self.parameters = SolverParameters(default=True)
        else:
            self.parameters = parameters

    @property
    def parameters(self):
        return self._parameters

    @parameters.setter
    def parameters(self, value):
        self._parameters = value

    def setup(self, graph):
        self.graph = graph

    def solve(self):
        # solve the problem
        bound = len(self.graph) + self._parameters["SATBound_offset"]
        problem = SATproblem(self.graph, bound)
        return problem.solve()


class LinkSolver(BaseSolver):
    """docstring for LinkSolver"""

    def __init__(self, parameters=None):
        super(LinkSolver, self).__init__(parameters)

    def setup(self, graph):
        # setup graph
        self.metaGraph = MetaGraph(graph,
                                   size=self._parameters["subGraph_size"])

    def solve(self, routeSet):
        subPaths = []
        startTime = time.time()
        for i, graph in enumerate(tqdm(self.metaGraph.subGraphs, ascii=True)):
            bound = len(graph) + self._parameters["SATBound_offset"]
            self.logger.info(f"building problem {i}")
            problem = SATproblem(graph, bound)
            counter = 0
            solved = False
            sTime = time.time()
            while not solved:
                if problem.solve(timeout=self.parameters["timeout"]):
                    solved = True
                    self.logger.info(f"solved in {time.time()-sTime} sec")
                    subPaths.append(problem.output()[0])
                else:
                    self.logger.info(f"problem {i} failed, increasing bound")
                    problem.bound += 1
                    problem.make()
                    counter += 1
                    solved = False
                # check counter
                if counter > self.parameters["maxProblems"]:
                    raise RuntimeError(f"problem {i} critically infeasible. "
                                       "graph may be degenerate")

        # build the meta graph
        self.logger.info("bullding pathGraph")
        self.metaGraph.buildPathGraph(subPaths)
        self.logger.info("linking routes")
        self.metaGraph.link(routeSet)
        # print time
        solTime = time.time()-startTime
        self.logger.info("solution time: {:2.5f} sec".format(solTime))
        return solTime
