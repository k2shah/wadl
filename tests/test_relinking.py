import pytest
import copy
# path
from pathlib import Path

# make sure relinked paths are same as those completely recalculated

@pytest.fixture
def stanford(speed):
    """test solver class """
    # build survey test fixture
    from wadl.survey import Survey
    from wadl.solver.solver import SolverParameters
    from wadl.lib.route import RouteParameters

    # make survey object
    path = Path(__file__).parent / "out"
    survey = Survey('stanford', path)
    file = Path(__file__).parent.parent / "example" / "data" / "stanford.csv"

    # make survey
    name = 'stanford'
    survey = Survey(name)

    # add the keypoints
    keyPoints = {"oval": (37.4298541, -122.1694745),
                "MSL":  (37.4266113, -122.173492)
                }
    survey.setKeyPoints(keyPoints)

    # route paramters
    routeParams = RouteParameters()
    routeParams["limit"] = 30*60,  # s
    routeParams["speed"] = speed  # m/s
    routeParams["altitude"] = 50.0  # m
    # add the tasks

    survey.addTask(file,
                step=100,
                home=["oval", "MSL"],
                routeParameters=routeParams,
                )

    # solver parameters
    solverParams = SolverParameters()
    solverParams["subGraph_size"] = 20
    solverParams["SATBound_offset"] = 4
    solverParams["timeout"] = 30

    # set the solver parameters
    survey.setSolverParamters(solverParams)

    return survey

def relink():
    '''
    resets route speed twice, and verifies new number of routes is same as would be originally recalculated
    '''
    from wadl.lib.route import RouteParameters
    file = Path(__file__).parent.parent / "example" / "data" / "stanford.csv"

    survey = stanford(5)

    survey.plan(write=False)

    initial = len(survey.tasks[file].routeSet)
    
    # reset route paramters
    routeParams = RouteParameters()
    routeParams["speed"] = 500  # m/s

    survey.relink(routeParams, showPlot=True)
    
    # corroborate with initial speed 500

    surveyComp = stanford(500)
    surveyComp.plan(write=False)

    # subtracts initial number of routes because routeSet isn't being rewritten during relinking
    secondary = len(survey.tasks[file].routeSet)-initial

    assert(len(surveyComp.tasks[file].routeSet) == len(survey.tasks[file].routeSet)-initial), "# routes mismatch"

    # reset route paramters
    routeParams = RouteParameters()
    routeParams["speed"] = 100  # m/s

    survey.relink(routeParams, showPlot=True)

    surveyComp = stanford(100)
    surveyComp.plan(write=False)

    assert(len(surveyComp.tasks[file].routeSet) == len(survey.tasks[file].routeSet)-initial-secondary), "# routes mismatch"
    



