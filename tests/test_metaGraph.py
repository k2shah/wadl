import pytest
# pathlib
from pathlib import Path
# graph
import networkx as nx
# plot


@pytest.fixture
def crozMetaGraphs():
    """test Maze class """
    # build fixture
    from wadl.solver.metaGraph import MetaGraph
    from wadl.lib.maze import Maze
    # cros test fixture
    file = Path(__file__).parent / "data" / "croz_west"

    sizes = [15, 20, 25, 27, 28, 30, 35, 40]
    metaGraphs = []
    for size in sizes:
        crozMaze = Maze(file,
                        step=40,
                        rotation=15)
        metaGraphs.append(MetaGraph(crozMaze.graph))
    return metaGraphs


def test_metaGraph(crozMetaGraphs):

    for metaGraph in crozMetaGraphs:
        subGraphSizes = sum([len(graph) for graph in metaGraph.subGraphs])
        assert len(metaGraph.baseGraph) == subGraphSizes


def test_metaGraph_connected(crozMetaGraphs):
    # detect not connected subgraphs
    for metaGraph in crozMetaGraphs:
        for graph in (metaGraph.subGraphs):
            assert(nx.is_connected(graph) is True)
