import pytest
# os
import os


@pytest.fixture
def survey():
    """test solver class """
    # build survey test fixture
    from wadl.survey import Survey
    solverParams = {"subGraph_size": 30,
                    "SATBound_offset": 4
                    }

    # make survey object
    path = os.path.join(os.path.dirname(__file__))
    outDir = os.path.join(path, "out")
    if not os.path.exists(outDir):
        os.makedirs(outDir)

    survey = Survey('test', outDir,
                    solverParam=solverParams)
    return survey


def test_island(survey):
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
    survey.addTask(file, step=35, flightParams=flightParams)
    survey.plan(plot=False)


def test_croz(survey):
    # get a island ("little norway")
    path = os.path.join(os.path.dirname(__file__), 'data')
    file = os.path.join(path, "croz_west")
    flightParams = {"limit":         12*60,  # s
                    "speed":         5.0,  # m/s
                    "altitude":      35.0,  # m
                    "xfer_speed":    12.0,  # m/s
                    "xfer_altitude": 70.0,  # m
                    "xfer_ascend":   5,  # m/s
                    "xfer_descend":  4,  # m/s
                    "land_altitude": 30,  # m
                    }
    survey.addTask(file, rotation=15, step=35, flightParams=flightParams)
    survey.plan(plot=False)
