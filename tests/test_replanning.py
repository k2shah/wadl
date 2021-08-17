import pytest
# path
from pathlib import Path

# make sure relinked paths are same as those completely recalculated

#@pytest.fixture
def stanford():
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
    routeParams["speed"] = 10  # m/s
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
    solverParams["stitch"] = "tree"

    # set the solver parameters
    survey.setSolverParamters(solverParams)

    return survey

def replan():
    '''
    resets route speed twice, and verifies new number of routes is same as would be originally recalculated
    '''
    from wadl.lib.route import RouteParameters
    file = Path(__file__).parent.parent / "example" / "data" / "stanford.csv"

    for i in range(1):
        survey = stanford()
        survey.plan(write=False)
        survey.partialComplete(0.4)
        survey.recompleteBFS()
        for _, maze in survey.tasks.items():
            metaGraph = survey.solvers[maze].metaGraph
            assert(metaGraph.oldTotal-metaGraph.merges==metaGraph.newTotal), "# merging error"
            print("success")

replan()