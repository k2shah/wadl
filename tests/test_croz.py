import pytest
# os
from pathlib import Path


@pytest.fixture
def croz():
    """test solver class """
    # build survey test fixture
    from wadl.survey import Survey
    from wadl.solver.solver import SolverParameters
    from wadl.lib.route import RouteParameters
    solverParams = SolverParameters()
    solverParams["subGraph_size"] = 30
    solverParams["SATBound_offset"] = 4

    # make survey object
    path = Path(__file__).parent / "out"
    survey = Survey('test', path)
    survey.setSolverParamters(solverParams)

    # get a island ("little norway")
    file = Path(__file__).parent / "data" / "croz_west"
    routeParams = RouteParameters()
    routeParams["limit"] = 13*60,  # s
    routeParams["speed"] = 5,  # m/s

    keyPoints = {"p": (-77.455917, 169.21753),
                 "c": (-77.454753, 169.216886),
                 "bn": (-77.44906, 169.22322),
                 "mle": (-77.45362, 169.23247),
                 "fg": (-77.459294, 169.245182)}
    survey.setKeyPoints(keyPoints)

    survey.addTask(file,
                   rotation=15,
                   step=30,
                   routeParameters=routeParams,
                   home=["c", "bn", "mle", "fg"]
                   )

    survey.plan(write=False)

    return survey


def test_group_home_mission(croz):
    from wadl.mission import Mission
    from wadl.mission import MissionParameters
    


