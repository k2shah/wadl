#!bin/bash/python3
# plot
import matplotlib.pyplot as plt
# wadl
from wadl.survey import Survey
from wadl.mission import Mission
# paramters
from wadl.solver.solver import SolverParameters
from wadl.lib.route import RouteParameters
from wadl.mission import MissionParameters

# suvey design script
# get file name
# files are assumed geofences (ID, lat, long)
file = "data/stanford.csv"


# PARAMETERS

keyPoints = {"oval": (37.4298541, -122.1694745),
             }

# route paramters
routeParams = RouteParameters()
routeParams["limit"] = 20*60,  # s
routeParams["speed"] = 5  # m/s
routeParams["altitude"] = 50.0  # m


# solver parameters
solverParams = SolverParameters()
solverParams["subGraph_size"] = 20
solverParams["SATBound_offset"] = 4
solverParams["timeout"] = 30

# mission paramters
missionParams = MissionParameters()
missionParams["nBands"] = 4
missionParams["autoLand"] = False


# make survey object and stars adding keypoints and tasks
name = 'stanford'
survey = Survey(name)

survey.setSolverParamters(solverParams)
survey.setKeyPoints(keyPoints)

survey.addTask(file,
               step=100,
               home="oval",
               routeParameters=routeParams,
               )

view = 0
# view current plan
if view == 1:
    survey.view()
else:
    # run path solver to plan paths and write output
    survey.plan(plot=True)

plt.savefig("routes.png", bbox_inches='tight', dpi=100)
plt.show()

# make mission
mission = Mission(missionParams)
mission.fromSurvey(survey)
mission.write()
