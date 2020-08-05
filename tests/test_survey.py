import pytest
# os
import os


@pytest.fixture
def island():
    """test solver class """
    # build survey test fixture
    from wadl.survey import Survey

    # make survey object
    path = os.path.join(os.path.dirname(__file__))
    outDir = os.path.join(path, "out")
    if not os.path.exists(outDir):
        os.makedirs(outDir)

    survey = Survey('test', outDir)
    return survey


def test_plan(island):
    # get a island ("little norway")
    path = os.path.join(os.path.dirname(__file__), 'data')
    file = os.path.join(path, "Little Norway")
    flightParams = {"limit":         5*60,  # s
                    "speed":         4.0,  # m/s
                    "altitude":      35.0,  # m
                    "xfer_speed":    12.0,  # m/s
                    "xfer_altitude": 70.0,  # m
                    "xfer_ascend":   5,  # m/s
                    "xfer_descend":  4,  # m/s
                    "land_altitude": 30,  # m
                    }
    island.addTask(file, step=35, flightParams=flightParams)
    island.plan(plot=False)
