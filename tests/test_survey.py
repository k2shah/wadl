import pytest
# os
from pathlib import Path


@pytest.fixture
def survey():
    """test solver class """
    # build survey test fixture
    from wadl.survey import Survey
    from wadl.solver.solver import SolverParameters
    solverParams = SolverParameters()
    solverParams["subGraph_size"] = 30
    solverParams["SATBound_offset"] = 4

    # make survey object
    path = Path(__file__).parent / "out"
    survey = Survey('test', path)
    survey.setSolverParamters(solverParams)
    return survey


def test_island(survey):
    from wadl.lib.route import RouteParameters
    # get a island ("little norway")
    file = Path(__file__).parent / "data" / "Little Norway"
    routeParams = RouteParameters()
    routeParams["limit"] = 5*60,  # s
    survey.addTask(file, step=35, routeParameters=routeParams)
    survey.plan()


def test_croz(survey):
    from wadl.lib.route import RouteParameters
    # get a island ("little norway")
    file = Path(__file__).parent / "data" / "croz_west"
    routeParams = RouteParameters()
    routeParams["limit"] = 5*60,  # s
    routeParams["speed"] = 5,  # m/s

    survey.addTask(file, rotation=15, step=35, routeParameters=routeParams)
    survey.plan()
