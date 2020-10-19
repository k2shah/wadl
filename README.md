# WADL
![build](https://github.com/k2shah/wadl/workflows/build/badge.svg)
[![docs](https://readthedocs.org/projects/wadl/badge/?version=latest)](https://wadl.readthedocs.io/en/latest/?badge=latest)
[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)

## Coverage Path Planner
<p float="center">
  <img src="https://github.com/k2shah/wadl/blob/devel/example/stanford/grid.png?raw=true" width=450 >
  <img src="https://github.com/k2shah/wadl/blob/devel/example/stanford/routes.png?raw=true" width=450 >
</p>


WADL is a python package for planning surveys over large areas using one or more UAV (Unpersoned Aerial Vehicle). WADL take in a geofence and desired gird spacing and produces a series of routes to survey the area inside the geofence. 

The project was motivated by the need for efficient route planning for multi-robot systems. WADL was designed and used in a 2019-2020 survey of 
Adélie penguins over [Cape Crozier, Ross Island, Antarctica](https://goo.gl/maps/wrMTuMq5kyNxZafx8) If you are interested in the technical details please see our paper <> 

This work was supported by grant XX

## Install
### pip
```
pip install wadl-planner
```
### source
```
git clone https://github.com/k2shah/wadl.git
pip install -r requirements.txt
```

## Usage
### Quick Start
```
from wadl.survey import Survey
survey = Survey()
survey.addTask(<path_to_geofence.csv>, step=100)
survey.plan()
```



see the [example](example/stanford.py) for a complete demonstration 

### Survey
Frist make a `Survey` object and set the output directory.

```
from wadl.survey import Survey
# make survey object
name = 'stanford'
survey = Survey(name)
survey.addTask(file, step=100)
```
Where `step` is the desired grid spacing. 

### Geofence
Next get the geofence file (csv). 
```
# files are assumed geofences (ID, lat, long)
file = <path_to_geofence.csv>
```

### Home 
Most surveys will have a predetermined takeoff/landing location known as the "home" point. A set of these key points can be added to the `Survey`. 
```
keyPoints = {"pt_0": (LAT_0, LONG_0),
             "pt_1": (LAT_1, LONG_1),
             }
survey.setKeyPoints(keyPoints)
```
### Task
Each survey is made up off a set of geofences, each geofence is referred to as a `Task` and expects a home point as the key in the `keyPoints` dictionary. Home points can be shared over multiple tasks. if no home is set, the default location is the most south eastern point. 
```
survey.addTask(file,
               step=100,
               home=KEY,
               routeParameters=routeParams,
               )
```


# Planning 
## Visualize
To visualize the current survey and tasks use
`survey.view()`

## Plan
To plan the survey use`survey.plan()`. To output the route to a csv pass `write=True` to the `plan()` method.

`survey.plot()` will output a plot of the survey paths.  


### Parameters
#### Route Parameters
As seen above, each task can have custom route parameters (flight speed, altitude). To set the parameters, import the `RouteParameters` object and set the desired values. The below values are the defaults
```
from wadl.lib.route import RouteParameters
routeParams = RouteParameters()
routeParams["limit"] = 13*60  # s flight time limit in seconds
routeParams["speed"] = 4.0  # m/s
routeParams["altitude"] = 35.0  # m
routeParams["xfer_speed"] = 12.0  # m/s
routeParams["xfer_altitude"] = 70.0  # m
routeParams["xfer_ascend"] = 5.  # m/s
routeParams["xfer_descend"] = 4.  # m/s
routeParams["land_altitude"] = 30  # m
```
#### Solver Parameters
WADL uses the [Z3 SMT prover from Microsoft Corporation](https://en.wikipedia.org/wiki/Z3_Theorem_Prover) to encode and solve the underlying route planning problem. Certain settings can be changed to better suit the user
```
from wadl.solver.solver import SolverParameters
solverParams = SolverParameters()

# the inital size of each subgraph, decrease for less powerful computer 
solverParams["subGraph_size"] = 40

# the inital offset of each subgraph path, increase for faster solve time (less efficient routes)
solverParams["SATBound_offset"] = 2

# timeout (in seconds) of each individual SMT problem 
solverParams["timeout"] = 60

# number of SMT problems attempted for each subgraph, limit increases by 1 for each infeasible subproblem
solverParams["maxProblems"] = 10
 ```
 


### UGCS
WADL has support to export route as a `mission.json` file to [ugcs](https://www.ugcs.com/)
```
from wadl.mission import Mission
mission = Mission(missionParams)
mission.fromSurvey(survey)
mission.write()
```
This creates a `mission.json` file that can be loaded into UGCS. This will also group the routes by sector to make it easier to field a multi-robot survey. This wiil also modify the transit altitude of the UAVS. The parameters can that be set are below. 

#### UGCS Version 
To set a UGCS version you can call
```
mission.setVersion(major, minor, build)
```
Where the ``major.minor.build`` is your version of UGCS

#### Mission Parameters

```
from wadl.mission import MissionParameters
missionParams = MissionParameters()

# will auto land the UAVs at the home position 
missionParams["autoland"] = True

# route organization 
# once routes are found, they can be organized and encoded into a mission JSON file for UGCS to open
# these options are for large surveys with multiple UAVs where coordination of the routes and their sequence is needed 

# grouping routes
missionParams["group"] = "home" ## other option is "task"

# sorting routes
# sorts the routes within a group with the following strategy
missionParams["sort"] = "angle" ## other option is "east" or "north"

# assigning routes
# routes can be assigned to bands either sequentially or sector
missionParams["assign"] = "sector ## other option is "sequence"


# offseting initial and final points
# offsets the takeoff location by this distance in m along the first segment 
missionParams["offset_takeoff_dist"] = 0

# offsets the land location by "bandRadialOffset" along the last segment 
missionParams["offset_land_dist"] = 0

# number of bands to split the sectors into (normally the number of UAVs used)
missionParams["N_bands"] = 1

# the started altitutde in m (agl)
missionParams["band_start"] = 50

# the altitte band seperation step
missionParams["band_step"] = 10
```

### Issues
For any suggestions or bugs please open an issue

### License
This software is licensed under [GNU GENERAL PUBLIC LICENSE verion 3](https://www.gnu.org/licenses/gpl-3.0)
