import pytest
# math
import numpy as np
import numpy.linalg as la
import numpy.random as rand
# plot
import matplotlib.pyplot as plt

@pytest.fixture
def croz():
    """test Fence class """
    # build fixture
    from wadl.lib.agent import Agents
    from wadl.lib.config import Config
    # cros test fixture
    starts = [0, 1]
    maxPath = 40
    step = 40
    agents = Agents(starts, maxPath)
    return Config('croz_west', agents, step)

def test_config(croz):
    # save figure to disk
    fig, ax = plt.subplots()
    croz.plot(ax)
    plt.savefig('tests/croz-grid.png') 
    # number of nodes and edges
    assert(len(croz.graph.nodes)==531), "nodes mismatch"
    assert(len(croz.graph.edges)==986), "edges mismatch"
