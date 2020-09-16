import pytest
# pathlib
from pathlib import Path
# graph
import networkx as nx
# plot


@pytest.fixture
def crozMetaGraph():
    """test Maze class """
    # build fixture
    from wadl.solver.metaGraph import MetaGraph
    from wadl.lib.maze import Maze
    # cros test fixture
    file = Path(__file__).parent / "data" / "croz_west"
    crozMaze = Maze(file,
                    step=40,
                    rotation=15)
    return MetaGraph(crozMaze.graph)


def test_metaGraph(crozMetaGraph):
    crozMetaGraph = crozMetaGraph
    subgraphSizes = [13, 18, 20, 29, 36, 41, 44, 36, 36, 10, 21,
                     11, 16, 26, 36, 36, 27, 32, 38, 25, 13]

    for graph, size in zip(crozMetaGraph.subGraphs, subgraphSizes):
        assert (len(graph) == size)

    # # save figure to disk
    # rootDir = os.path.dirname(__file__)
    # pathDir = os.path.join(rootDir, "out")

    # fig, ax = plt.subplots()
    # colors = crozMetaGraph.getCols()
    # crozMaze.plot(ax, showGrid=False)
    # if not os.path.exists(pathDir):  # make dir if not exists
    #     os.makedirs(pathDir)
    # for i, graph in enumerate(crozMetaGraph.subGraphs):
    #     # print(graph.nodes)
    #     col = next(colors)
    #     # print(colors[colIdx])
    #     crozMaze.plotNodes(ax, nodes=graph.nodes, color=col)
    # fileName = os.path.join(pathDir, 'croz-metaGraph.png')
    # plt.savefig(fileName)


def test_metaGraph_connected(crozMetaGraph):
    # detect not connected subgraphs
    for graph in (crozMetaGraph.subGraphs):
        assert(nx.is_connected(graph) is True)
