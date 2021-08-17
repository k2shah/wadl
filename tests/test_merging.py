import pytest
# path
from pathlib import Path
import copy

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
    routeParams["speed"] = 5  # m/s
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

def fillRoute(survey,maze,route):
    metaGraph = survey.solvers[maze].metaGraph
    route.setMaze(maze)
    cords = route.UTMcords[:len(route.UTMcords)-1]
    i=0
    while i < len(route.UTMcords)-1:
        prev = len(route.UTMcords)
        route.unstreamline(metaGraph, i)
        delta = len(route.UTMcords)-prev
        i += 1 + delta


def replan():
    '''
    resets route speed twice, and verifies new number of routes is same as would be originally recalculated
    '''
    from wadl.lib.route import RouteParameters
    file = Path(__file__).parent.parent / "example" / "data" / "stanford.csv"

    survey1 = stanford()
    survey1.plan(write=False)
    prevs = []
    news=[]
    difs=[]
    for i in range(100):
        survey = copy.deepcopy(survey1)
        nodes = []
   

        unreachedNodes = []

        survey.partialComplete(0.7)

        print("before recompletion")

        metaGraph = None
        
        for _, maze in survey.tasks.items():
            # setup survey
            metaGraph = survey.solvers[maze].metaGraph
            metaGraph.setMaze(maze)
            for n in maze.graph.nodes:
                unreachedNodes.append(n)

            print("--------------------prev nodes: ", len(unreachedNodes))
            print("length: ", len(maze.routeSet.routes))
            for route in maze.routeSet.routes:
                fillRoute(survey,maze,route)
                g = []
                # verify every node is reached
                for pt in route.UTMcords:
                    gridPt = maze.UTM2Grid[(int(pt[0]),int(pt[1]))]
                    g.append(gridPt)
                    if gridPt in unreachedNodes:
                        unreachedNodes.remove(gridPt)
            print("--------------------old nodes: ", len(unreachedNodes))

        #survey.plot()

        prev, new = survey.recompleteBFS()
        prevs.append(prev)
        news.append(new)
        difs.append(prev-new)

        #survey.plot()

        print("after recomplete")

        for _, maze in survey.tasks.items():
            # setup survey
            metaGraph = survey.solvers[maze].metaGraph
            print("--------------------prev nodes: ", len(unreachedNodes))
            print("length: ", len(maze.routeSet.routes))
            for route in maze.routeSet.routes:
                fillRoute(survey,maze,route)
                g = []
                # verify every node is reached
                for pt in route.UTMcords:
                    gridPt = maze.UTM2Grid[(int(pt[0]),int(pt[1]))]
                    g.append(gridPt)
                    if gridPt in unreachedNodes:
                        unreachedNodes.remove(gridPt)
                print(g)
            print("--------------------old nodes: ", len(unreachedNodes))
            print(unreachedNodes)
            assert(len(unreachedNodes)==0), "# merging error"
            # uncomp = []
            # for n in unreachedNodes:
            #     uncomp.append((metaGraph.getUTM(n)[0],metaGraph.getUTM(n)[1]))
            # _, new = maze.routeSet.check(uncomp)
            # maze.routeSet.routes = []
            # maze.routeSet.push(new)
            # survey.plot()
    print("prev", sum(prevs)/len(prevs))
    variance = sum([((x - sum(prevs)/len(prevs)) ** 2) for x in prevs]) / len(prevs)
    res = variance ** 0.5
    print(res)
    print("news", sum(news)/len(news))
    variance = sum([((x - sum(news)/len(news)) ** 2) for x in news]) / len(news)
    res = variance ** 0.5
    print(res)
    print("difs", sum(difs)/len(difs))
    variance = sum([((x - sum(difs)/len(difs)) ** 2) for x in difs]) / len(difs)
    res = variance ** 0.5
    print(res)
        

replan()