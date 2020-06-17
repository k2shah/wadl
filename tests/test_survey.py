import pytest
# os
import os
# plot
import matplotlib.pyplot as plt

@pytest.fixture
def island():
    """test solver class """
    # build survey test fixture
    from wadl.lib.survey import Survey

    # make survey object
    path = os.path.join(os.path.dirname( __file__ ))
    outDir = os.path.join(path, "out")
    if not os.path.exists(outDir):
        os.makedirs(outDir)

    survey = Survey('test', outDir)
    return survey

def test_plan(island):
    # get a island ("little norway")
    path = os.path.join(os.path.dirname( __file__ ), 'data')
    file = os.path.join(path, "Little Norway")
    absfile = os.path.abspath(file)
    island.addTask(file, step=35, limit=41)
    island.plan(plot=False)