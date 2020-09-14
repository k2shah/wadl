#!bin/bash/python3
import os.path as osp
import glob
# import time
# math
# plot
import matplotlib.pyplot as plt
# lib
from wadl.survey import Survey
from wadl.mission import Mission
# paramters
from wadl.solver.solver import SolverParameters
from wadl.lib.route import RouteParameters
from wadl.mission import MissionParameters

# suvey design script
# get list of areas to survey
rootDir = osp.dirname(__file__)
dataDir = osp.join(rootDir, "data")
# files are assumed geofences (ID, lat, long)
# get file name
filename = "stanford.csv"
# resolve path
file = osp.join(rootDir, "data", filename)


# PARAMETERS

keyPoints = {"oval": (37.4301388, -122.1688323),
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
outDir = osp.join(rootDir, 'out')
survey = Survey(name, outDir)
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

plt.show()

# make mission
mission = Mission(missionParams)
mission.fromSurvey(survey)
mission.write()