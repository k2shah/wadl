import pytest
# os
import os
# plot
import matplotlib.pyplot as plt


@pytest.fixture(scope="session")
def crozMaze():
    """test Maze class """
    # build fixture
    from wadl.lib.maze import Maze
    # cros test fixture
    path = os.path.join(os.path.dirname(__file__), 'data')
    file = os.path.join(path, "croz_west")
    absfile = os.path.abspath(file)
    return Maze(absfile,
                step=40,
                rotation=15)


def test_maze(crozMaze):
    # number of nodes and edges
    assert(len(crozMaze.graph.nodes) == 564), "nodes mismatch"
    assert(len(crozMaze.graph.edges) == 1048), "edges mismatch"

    # save figure to disk
    fig, ax = plt.subplots()
    crozMaze.plot(ax, showGrid=True)
    rootDir = os.path.dirname(__file__)
    pathDir = os.path.join(rootDir, "out")
    if not os.path.exists(pathDir):  # make dir if not exists
        os.makedirs(pathDir)
    fileName = os.path.join(pathDir, 'croz-grid.png')
    plt.savefig(fileName)
