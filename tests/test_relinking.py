import pytest
import copy
# path
from pathlib import Path

# make sure relinked paths are same as those completely recalculated


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

    secondary = len(survey.tasks[file].routeSet)-initial

    print(len(surveyComp.tasks[file].routeSet))
    print(len(survey.tasks[file].routeSet)-initial)

    # reset route paramters
    routeParams = RouteParameters()
    routeParams["speed"] = 100  # m/s

    survey.relink(routeParams, showPlot=True)

    surveyComp = stanford(100)
    surveyComp.plan(write=False)

    print(len(surveyComp.tasks[file].routeSet))
    print(len(survey.tasks[file].routeSet)-initial-secondary)

    '''
    relinked = []
    original = []

    for speed in speeds:
        routeParams = RouteParameters()
        routeParams["speed"] = speed  # m/s

        survey.relink(routeParams)

        surveyComp = stanford(speed)
        surveyComp.plan(write=False)

        if (len(relinked) != 0):
            relinked.append(len(survey.tasks[file].routeSet) - relinked[-1])
        else:
            relinked.append(len(survey.tasks[file].routeSet)/2)
        original.append(len(surveyComp.tasks[file].routeSet))

    print(original)
    print(relinked)
    '''
    
    

relink()





