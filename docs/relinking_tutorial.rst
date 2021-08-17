Relinking
========
We demonstrate a re-planning method to adjust UAV path parameters without 
reconstructing UAV routes. During surveys, you may want to adjust route parameters
without replanning entire UAV paths. For example, you might need to quickly change
UAV max speed or altitude in the field. This relinking method allows one to alter
route parameters, then relink paths without calling the time-consuming solver. This
tutorial explains how to create a survey, and perform relinking.

Survey
------
First make a ``Survey`` object and plan initial UAV paths
::

    from wadl.survey import Survey
    # make survey object
    name = 'stanford'
    survey = Survey(name)

    # files are assumed geofences (ID, lat, long)
    file = <path_to_geofence.csv>

    keyPoints = {"pt_0": (LAT_0, LONG_0),
                 "pt_1": (LAT_1, LONG_1),
                 }
    survey.setKeyPoints(keyPoints)

    # set the initial route parameters (may want to be changed later)
    from wadl.lib.route import RouteParameters
    routeParams = RouteParameters()
    routeParams["limit"] = 13*60  # s flight time limit in seconds
    routeParams["speed"] = 4.0  # m/s

    # add all desired tasks
    survey.addTask(file,
                   step=100,
                   home=KEY,
                   routeParameters=routeParams,
                   )

    # finally, plan paths for the original survey.
    survey.plan()

You now have a complete Survey object with pre-planned UAV paths.

Route Parameters
++++++++++++++++
As seen above, each task can have custom route parameters (flight speed, altitude).
To change routeParameters after planning, set each new value. Below are the default
values.
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

Relinking
++++++++++++++++
Set the new route parameters, replan paths, and visualize
::
    survey.relink(routeParams)
    survey.plot()