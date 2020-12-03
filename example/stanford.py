#!bin/bash/python3
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

# make survey
name = 'stanford'
survey = Survey(name)

# add the keypoints
keyPoints = {"oval": (37.4298541, -122.1694745),
             "MSL":  (37.4266113, -122.173492)
             }
survey.setKeyPoints(keyPoints)

# route parameters
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

# plan the survey
view = 0
# view current plan
if view == 1:
    survey.view()
else:
    # run path solver to plan paths and write output
    survey.plan(showPlot=True)
    # survey.plot()

# make mission
# mission parameters
# missionParams = MissionParameters()
# missionParams["N_bands"] = 3
# missionParams["autoland"] = False

# missionParams["assign"] = "sequence"

# missionParams["offset_takeoff_dist"] = 10
# missionParams["offset_land_dist"] = 10


# mission = Mission(missionParams)
# mission.fromSurvey(survey, showPlot=True)
# mission.setVersion(4, 0, 187)
# mission.write()
