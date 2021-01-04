import pytest
# os
from pathlib import Path


@pytest.fixture
def island():
    """test solver class """
    # build survey test fixture
    from wadl.survey import Survey
    from wadl.solver.solver import SolverParameters
    solverParams = SolverParameters()
    solverParams["subGraph_size"] = 30
    solverParams["SATBound_offset"] = 4

    # make survey object
    path = Path(__file__).parent / "out"
    survey = Survey('island', path)
    survey.setSolverParamters(solverParams)
    from wadl.lib.route import RouteParameters
    # get a island ("little norway")
    file = Path(__file__).parent / "data" / "Little Norway"
    routeParams = RouteParameters()
    routeParams["limit"] = 7*60.  # s
    survey.addTask(file, step=35, routeParameters=routeParams)
    survey.plan()

    return survey


def test_no_home(island):
    from wadl.mission import Mission
    from wadl.mission import MissionParameters

    missionParams = MissionParameters()
    # will auto land the UAVs at the home position
    # missionParams["autoland"] = False
    # # offsets the takeoff location along the 1st segment
    missionParams["offsetTakeoff"] = 10
    # # offsets the land location along the 1st segment
    # missionParams["offsetLand"] = 0

    missionParams["group"] = "home"
    missionParams["assign"] = "sequence"
    # # number of bands to split the sectors into (normally the number of UAVs used)
    missionParams["N_bands"] = 2
    # the started altitutde in m (agl)
    missionParams["band_start"] = 50
    # the altitte band seperation step
    missionParams["band_step"] = 10

    # missionParams["trajectory_type"] = "safe"

    mission = Mission(missionParams)
    mission.fromSurvey(island)
