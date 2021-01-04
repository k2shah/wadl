# gen
import time
import logging
# lib
from wadl.solver.SATproblem import SATproblem
from wadl.solver.metaGraph import MetaGraph
from wadl.solver.pathTree import PathTree
from wadl.solver.pathTreeMilp import PathTreeMilp
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
        self["stitch"] = "default"


class BaseSolver(object):
    """docstring for Solver"""

    def __init__(self, parameters=None):
        # logging
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)

        # parameters
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

    def metaGraphSelect(self):
        # select MetaGraph type
        if self.parameters["stitch"] == "default":
            metaGraphClass = MetaGraph
        elif self.parameters["stitch"] == "tree":
            metaGraphClass = PathTree
        elif self.parameters["stitch"] == "milp":
            metaGraphClass = PathTreeMilp
        else:
            self.logger.warm(f"{self.parameters['stitch']} is not valid")
            metaGraphClass = MetaGraph
        return metaGraphClass

    def setup(self, graph):
        metaGraphClass = self.metaGraphSelect()
        # setup graph
        self.metaGraph = metaGraphClass(graph,
                                        size=self._parameters["subGraph_size"])

    def solve(self, routeSet):
        startTime = time.time()
        # solve each tile
        subPaths = self.solveTiles()
        # merge tiles based on the metaGraph selection
        self.mergeTiles(subPaths, routeSet)
        # return solution time
        solveTime = time.time()-startTime
        self.logger.info("solution time: {:2.5f} sec".format(solveTime))
        routeSet.setData(self.getRouteData())
        return solveTime

    def getRouteData(self):
        data = dict()
        # calculate various metrics and push them to the routeSet container
        data["nGraphs"] = len(self.metaGraph.subGraphs)
        data["nSteps"] = sum([len(path)-1 for path in self.metaGraph.subPaths])
        return data

    def solveTiles(self):
        subPaths = []
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
        return subPaths

    def mergeTiles(self, subPaths, routeSet):
        # build the meta graph
        self.logger.info("bullding pathGraph")
        self.metaGraph.buildPathGraph(subPaths)
        self.logger.info("linking routes")
        self.metaGraph.link(routeSet)
