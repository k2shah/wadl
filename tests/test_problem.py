import pytest
# graph
import networkx as nx


@pytest.fixture
def gridGraph():
    """test solver class """
    # creata a random grid graph
    size = [4, 4]
    gridGraph = nx.grid_graph(dim=size)
    # save the index of each node
    for i, node in enumerate(gridGraph):
        gridGraph.nodes[node]['index'] = i
    return gridGraph


def test_problem(gridGraph):
    # get the limit , should be able to solve in 17 steps
    bound = len(gridGraph) + 1
    from wadl.solver.SATproblem import SATproblem
    problem = SATproblem(gridGraph, bound=bound)
    solved, paths, solTime = problem.solve()
    assert(solved is True)
