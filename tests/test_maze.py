import pytest
# pathlib
from pathlib import Path
# plot
import matplotlib.pyplot as plt


@pytest.fixture(scope="session")
def crozMaze():
    """test Maze class """
    # build fixture
    from wadl.lib.maze import Maze
    # cros test fixture
    file = Path(__file__).parent / "data" / "croz_west"
    return Maze(file,
                step=40,
                rotation=15)


def test_maze(crozMaze):
    # number of nodes and edges
    assert(len(crozMaze.graph.nodes) == 564), "nodes mismatch"
    assert(len(crozMaze.graph.edges) == 1048), "edges mismatch"

    # save figure to disk
    fig, ax = plt.subplots()
    crozMaze.plot(ax, showGrid=True)
    pathDir = Path(__file__).parent / "out"
    pathDir.mkdir(exist_ok=True)  # make dir if not exists
    fileName = pathDir / 'croz.png'
    plt.gca().set_aspect('equal', adjustable='box')
    plt.savefig(fileName, bbox_inches='tight', dpi=200)
