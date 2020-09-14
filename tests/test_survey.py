import pytest
# os
import os


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
    path = os.path.join(os.path.dirname(__file__))
    outDir = os.path.join(path, "out")
    if not os.path.exists(outDir):
        os.makedirs(outDir)

    survey = Survey('test', outDir)
    survey.setSolverParamters(solverParams)
    return survey


def test_island(survey):
    from wadl.lib.route import RouteParameters
    # get a island ("little norway")
    path = os.path.join(os.path.dirname(__file__), 'data')
    file = os.path.join(path, "Little Norway")
    routeParams = RouteParameters()
    routeParams["limit"] = 5*60,  # s
    survey.addTask(file, step=35, routeParameters=routeParams)
    survey.plan(plot=False)


def test_croz(survey):
    from wadl.lib.route import RouteParameters
    # get a island ("little norway")
    path = os.path.join(os.path.dirname(__file__), 'data')
    file = os.path.join(path, "croz_west")
    routeParams = RouteParameters()
    routeParams["limit"] = 5*60,  # s
    routeParams["speed"] = 5,  # m/s

    survey.addTask(file, rotation=15, step=35, routeParameters=routeParams)
    survey.plan(plot=False)
