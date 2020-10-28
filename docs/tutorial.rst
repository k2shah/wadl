.. _tutorial:

Tutorial
========


Survey
------
First make a ``Survey`` object. An optional ``name`` can be specified. 
::

    from wadl.survey import Survey
    # make survey object
    name = 'stanford'
    survey = Survey(name)

Geofence
++++++++
Next get the geofence file (csv).
::

    # files are assumed geofences (ID, lat, long)
    file = <path_to_geofence.csv>

Home
++++
Most surveys will have a predetermined takeoff/landing location known as the "home" point. A set of these key points can be added to the `Survey`.
::

    keyPoints = {"pt_0": (LAT_0, LONG_0),
                 "pt_1": (LAT_1, LONG_1),
                 }
    survey.setKeyPoints(keyPoints)

Task
+++++
Each survey is made up off a set of geofences, each geofence is referred to as a `Task` and expects a home point as the key in the `keyPoints` dictionary. Home points can be shared over multiple tasks. if no home is set, the default location is the most south eastern point.
::

    survey.addTask(file,
                   step=100,
                   home=KEY,
                   routeParameters=routeParams,
                   )

Where ``step`` is the desired grid spacing. 

Planning 
--------
Visualize
+++++++++
To visualize the current survey and tasks use
::

    survey.view()

Plan
++++
To plan and plot the survey use
::

    survey.plan()
    survey.plot() 

Routes are planned in such a way that the segments between the home and coverage section are at a different altitude than the altitude of the survey.

The routes are composed as follows:
home - transfer to site -coverage path - transfer to home - land (optional).

Parameters
----------
Route Parameters
++++++++++++++++
As seen above, each task can have custom route parameters (flight speed, altitude). To set the parameters, import the ``RouteParameters`` object and set the desired values. The below values are the defaults
::

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

Solver Parameters
+++++++++++++++++
WADL uses the Z3_ SMT prover from Microsoft Corporation
to encode and solve the underlying route planning problem. Certain settings can be changed to better suit the user. To set the parameters, import the ``SolverParameters`` object and set the desired values. The below values are the defaults.

.. _Z3: (https://en.wikipedia.org/wiki/Z3_Theorem_Prover) 

::

    from wadl.solver.solver import SolverParameters
    solverParams = SolverParameters()
    # the initial size of each subgraph, decrease for less powerful computer 
    solverParams["subGraph_size"] = 40
    # the initial offset of each subgraph path, increase for faster solve time (less efficient routes)
    solverParams["SATBound_offset"] = 2\
    # timeout (in seconds) of each individual SMT problem 
    solverParams["timeout"] = 60\
    # number of SMT problems attempted for each subgraph, limit increases by 1 for each infeasible subproblem
    solverParams["maxProblems"] = 10


After setting the solver parameters set them by calling the ``.setSolverParameters()`` method of the ``survey`` object.

UGCS
-----
WADL has support to export route as a ``mission.json`` file to UGCS_.

.. _UGCS: (https://www.ugcs.com/)

::

    from wadl.mission import Mission
    mission = Mission(missionParams)
    mission.fromSurvey(survey)
    mission.write()

This creates a ``mission.json`` file that can be loaded into UGCS. This will also group the routes by sector to make it easier to field a multi-robot survey. This will also modify the transit altitude of the UAVS. The parameters can that be set are below. 

UGCS Version 
++++++++++++
To set a UGCS version you can call
::

    mission.setVersion(major, minor, build)

Where the ``major.minor.build`` is your version of UGCS

Mission Parameters
++++++++++++++++++
To set the parameters, import the ``MissionParameters`` object.
::

    from wadl.mission import MissionParameters
    missionParams = MissionParameters()


Autoland
********
Auto land the UAVs at the home position 
::

    missionParams["autoland"] = True

You can also set a pre landing altitude where the UAV will go to this altitude after the last point in the route
::

    missionParams["pre_land_alt"] = None  # m

Route Organization 
******************
Once routes are found, they can be organized and encoded into a mission JSON file for UGCS to open. These options are for large surveys with multiple UAVs where coordination of the routes and their sequence is needed 

Group Routes::

    # group the routes 
    missionParams["group"] = "home" ## other option is "task"

Sort Routes::

    # sorting routes
    # sorts the routes within a group with the following strategy
    missionParams["sort"] = "angle" ## other option is "east" or "north"

Assign Routes::

    # assigning routes
    # routes can be assigned to bands either sequentially or sector
    missionParams["assign"] = "sector" ## other option is "sequence"

Offset Routes
*************
Offset the start and end of the route a certain amount from the home point, this make it easier to have multiple UAVs have the same home point
::

    # offsets the takeoff location by this distance in m along the first segment 
    missionParams["offset_takeoff_dist"] = 0

    # offsets the land location by this distance in m along the last segment 
    missionParams["offset_land_dist"] = 0

Altitude Bands
**************
You can set the number of bands to split (normally the number of UAVs used) the UAV transfer altitude into as well as the starting transfer altitude and band separation altitude
::

    missionParams["N_bands"] = 1

    # the started altitude in m (agl)
    missionParams["band_start"] = 50

    # the altitude band separation step
    missionParams["band_step"] = 10
