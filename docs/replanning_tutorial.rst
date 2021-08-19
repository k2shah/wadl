Relinking
========
We demonstrate a re-planning method to replan new UAV paths during robot malfunction. 
Issues often arise in the field, and since UAVs are operated in inclement conditions
they may fail before or during surveys due to unexpected battery drain, SD card malfunctions,
obscured cameras, or other reasons. This method allows us to recover uncompleted paths,
and partition them together for a secondary UAV survey. We use a breadth-first-expansion
approach to partition UAV paths based on distance from home points.


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

Robot malfunction
------
Unfortunately, you may have to replan robot paths during malfunction.

Call ``survey.uncomplete`` to input information about UAV malfunction. ``survey.uncomplete``
accepts a dictionary that maps failed route numbers to points of malfunction. In tshis
example, route 1 failed at point 23 and route 7 failed at point 42.
::
    uncompleted = dict()
    uncompleted[1] = 23
    uncompleted[7] = 42
    survey.uncomplete(uncompleted)
    # visualize routes
    survey.plot()

Plan new routes to survey the uncompleted points.
::

    survey.recompleteBFS()
    # visualize new routes
    survey.plot()