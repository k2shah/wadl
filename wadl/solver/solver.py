# gen
import time
# lib
from wadl.solver.SATproblem import SATproblem
from wadl.solver.metaGraph import MetaGraph
from tqdm import tqdm


class BaseSolver(object):
    """docstring for Solver"""

    def __init__(self, **kwargs):
        self.parameters = kwargs

    def setup(self, graph):
        self.graph = graph

    def solve(self):
        # solve the problem
        bound = len(self.graph) + self.parameters["SATBound_offset"]
        problem = SATproblem(self.graph, bound)
        return problem.solve()


class LinkSolver(BaseSolver):
    """docstring for LinkSolver"""

    def __init__(self, subGraph_size=40, SATBound_offset=2):
        super(LinkSolver, self).__init__()
        self.parameters["subGraph_size"] = subGraph_size
        self.parameters["SATBound_offset"] = SATBound_offset

    def setup(self, graph):
        # setup graph
        self.metaGraph = MetaGraph(graph,
                                   size=self.parameters["subGraph_size"])

    def solve(self, routeSet):
        subPaths = []
        startTime = time.time()
        for i, graph in enumerate(tqdm(self.metaGraph.subGraphs, ascii=True)):
            bound = len(graph) + self.parameters["SATBound_offset"]
            print(f"\tbuilding problem {i}")
            problem = SATproblem(graph, bound)
            counter = 0
            solved = False
            sTime = time.time()
            while not solved:
                if problem.solve(timeout=60):
                    solved = True
                    print(f"\t\tsolved in {time.time()-sTime} sec")
                    subPaths.append(problem.output()[0])
                else:
                    print(f"\t\tproblem {i} failed, increasing bound")
                    problem.bound += 1
                    problem.make()
                    counter += 1
                    solved = False
                # check counter
                if counter > 10:
                    raise RuntimeError(f"\tproblem {i} critically infeasible. "
                                       "graph may be degenerate")

        # build the meta graph
        print("\tbullding pathGraph")
        self.metaGraph.buildPathGraph(subPaths)
        print("\tlinking routes")
        self.metaGraph.link(routeSet)
        # print time
        solTime = time.time()-startTime
        print("\tsolution time: {:2.5f} sec".format(solTime))
        return solTime
