# gen
import time
import warnings
from collections import defaultdict
# io
import json
from pathlib import Path
# gis
import utm
# math
import numpy as np
# plot
import matplotlib.pyplot as plt
# lib
from wadl.lib.parameters import Parameters


class MissionParameters(Parameters):
    """Parameter container for seting missions parameters

    Set paramters directly like how you would for a dictionary.
    ``missionParameters = MissionParameters``
    ``missionParameters["Paramter"] = value``

    Args:
        autoland (bool): land after route
        pre_land_alt (float): lower to this alt after route
        trajectory_type (str): "straight", or "safe"
        group (str): grouping option "home" or "task"
        sort (str): sorting option "angle", "north", or "east"
        assign (str): assignment option
        N_bands (int): number of altitude bands
        band_start (float): starting altitude band
        band_step (float): step for the altiude bands
        offset_takeoff_dist (float): takeoff offset distance in (m)
        offset_landf_dist (float): land offset distance in (m)

    """

    def __init__(self, default=True):
        super(MissionParameters, self).__init__(default)

    def setDefaults(self):
        self["autoland"] = False
        self["pre_land_alt"] = None  # m
        self["trajectory_type"] = "straight"
        self["trajectory_resolver"] = {"straight": "STRAIGHT",
                                       "safe": "STAIR"}

        # export options
        self["group"] = "home"
        self["sort"] = "angle"
        self["assign"] = 'sector'

        # band grouping
        self["N_bands"] = 1
        self["band_start"] = 50
        self["band_step"] = 10

        # offset from home, requires a not NONE home
        self["offset_takeoff_dist"] = 0
        self["offset_land_dist"] = 0


class Mission(object):
    """Creates a UGCS mission from a survey

    Args:
        missionParamters (MissionParamters): Parameters for the mission

    """

    def __init__(self, missionParamters=None):
        self.outDir = ""
        self.name = "mission"

        if missionParamters is None:
            # get default
            self.paramters = MissionParameters()
        else:
            self.parameters = missionParamters

        self.data = {"version": {},
                     "payloadProfiles": [],
                     "vehicleProfiles": [self.DJIprofile()],
                     "mission": {},
                     "vehicles": []
                     }

        self.autoland = self.parameters["autoland"]
        # altitude bands for vertical seperation
        self.nBands = self.parameters["N_bands"]
        bandStep = self.parameters["band_step"]
        bandStart = self.parameters["band_start"]
        self.bands = bandStart +\
            np.linspace(0, (self.nBands-1)*bandStep, self.nBands)

        self.setVersion()

    def write(self):
        """Writes the mission routes and json file

        """
        filename = self.outDir / "mission.json"
        with filename.open('w') as f:
            json.dump(self.data, f,
                      indent=2, separators=(',', ': '))

    def setVersion(self, major=3, minor=6, build=225):
        """set the version of UGSC as major.minor.build

        Args:
            major (int): major version
            minor (int): minor version
            build (int): build version


        """
        version = {"major": major,
                   "minor": minor,
                   "build": build,
                   "component": "DATABASE"
                   }
        self.data["version"] = version

    def fromSurvey(self, survey, showPlot=False):
        """ import routes from a Survey

        Args:
            survey (wadl.Survey): Survey object.

            showPlot (bool, optional): show the plot of the modified routes.

        """
        self.name = survey.name
        self.outDir = survey.outDir
        # plot new ordering
        self.showPlot = showPlot

        # build mission.json header
        self.buildMission()
        # oraganze and build routes
        self.buildRoutes(survey)

    def fromDirc(self, srcDir):
        raise NotImplementedError()

    def buildMission(self):
        mission = {"name": self.name,
                   "description": None,
                   "creationTime": int(time.time())}
        self.data["mission"] = mission

    def buildRoutes(self, survey):
        routes = self.groupRoutes(survey)
        routes = self.sortRoutes(routes)

        # start plottng
        fig, ax = plt.subplots(figsize=(16, 16))
        survey.plotKeyPoints(ax)
        cols = plt.cm.rainbow_r(np.linspace(0, 1, self.nBands))
        for task, maze in survey.tasks.items():
            maze.plot(ax, showRoutes=False)

        # write routes to json and file
        path = Path(self.outDir, "routes")
        path.mkdir(exist_ok=True)
        routeList = []
        for g, key in enumerate(routes):
            nRoutes = len(routes[key])
            if self.parameters["assign"] == "sector":
                b = int(nRoutes/self.nBands)
                r = nRoutes % self.nBands
                s = r*(b+1)
                assigned = (int(i/(b+1)) if i < s else int((i-s)/b)+r
                            for i in range(nRoutes))

            elif self.parameters["assign"] == "sequence":
                assigned = (int(i % self.nBands) for i in range(nRoutes))
            else:
                raise RuntimeError(f"param error")

            for i, (route, assignIdx) in enumerate(zip(routes[key], assigned)):
                altBand = self.bands[assignIdx]
                name = f"{key}_{i+1}_{int(altBand)}"

                # encode route
                routeList.append(self.makeRoute(name, route.waypoints,
                                                altBand, route.home))

                # plot route
                route.plot(ax, cols[assignIdx])

                # write route
                filename = self.outDir / "routes" / f"{name}.csv"
                route.write(filename)
        # save the json encoded route list
        self.data["mission"]["routes"] = routeList

        # output plot
        plt.axis('square')
        plt.gca().set_aspect('equal', adjustable='box')
        filename = self.outDir / "mission_routes.png"
        plt.savefig(filename, bbox_inches='tight', dpi=100)
        if self.showPlot:
            plt.show()

    def groupRoutes(self, survey):
        # group all the routes
        routes = defaultdict(list)
        # reverse the keyPoints dict to be (gps) -> key
        keyPoints_rev = {v: i for i, v in survey.keyPoints.items()}
        # get all the routes in the survey (from each maze)
        for task, maze in survey.tasks.items():
            if maze.routeSet.home is None:
                warnings.warn("no home found. Disabling autoland & offsets")
                self.autoland = False
                self.parameters["offset_takeoff_dist"] = 0
                self.parameters["offset_land_dist"] = 0
                self.parameters['group'] == "task"
            # group into dictionary
            for i, route in enumerate(maze.routeSet.routes):
                # name = maze.name + "_" + str(i)
                if self.parameters['group'] == "home":
                    if route.home is None:
                        homeKey = None
                    else:
                        homeKey = keyPoints_rev[route.home]
                    routes[homeKey].append(route)
                elif self.parameters['group'] == "task":
                    routes[maze.name].append(route)
                else:
                    raise RuntimeError(f"param error")
        return routes

    def sortRoutes(self, routes):
        # sort routes by option
        if self.parameters["sort"] == "angle":
            sortFunc = self.headingAngle
        elif self.parameters["sort"] == "east":
            sortFunc = self.eastStart
        elif self.parameters["sort"] == "north":
            sortFunc = self.northStart
        else:
            raise RuntimeError(f"param error")
        for key in routes:
            routes[key].sort(key=sortFunc)

        return routes

    # route sorting methods
    @staticmethod
    def headingAngle(route):
        # returns the inital heading angle of a route
        wp = route.waypoints
        angle = np.arctan2(wp[1][1]-wp[0][1],
                           wp[1][0]-wp[0][0])
        return (angle + 2 * np.pi) % (2 * np.pi)

    @staticmethod
    def eastStart(route):
        # returns the easting of the starting point
        route.GPS2UTM()
        return route.UTMcords[0][0]

    @staticmethod
    def eastStart(route):
        # returns the northing of the starting point
        route.GPS2UTM()
        return route.UTMcords[0][1]

    def offsetHome(self, home, pt, dist):
        # returns a pt dist meters from the home along home-pt
        home_utm = utm.from_latlon(*home)
        pt_utm = utm.from_latlon(*pt[:2])

        zone_utm = home_utm[2:]
        vec = np.array(pt_utm[:2])-np.array(home_utm[:2])

        # normalize and scale
        vec = vec/np.linalg.norm(vec) * dist
        offsetPt = np.array(home_utm[:2]) + vec
        lat, lng = utm.to_latlon(*offsetPt, *zone_utm)
        return [lat, lng, *pt[2:]]

    # helper functions to build the waypoint lists
    def makeRoute(self, name, route, bandAlt=None, home=None):
        failsafe = {"rcLost": "GO_HOME",
                    "gpsLost": None,
                    "lowBattery": None,
                    "datalinkLost": None
                    }

        routeJson = {"name": name,
                     "creationTime": int(time.time()),
                     "scheduledTime": None,
                     "startDelay": None,
                     "vehicleProfile": "DJI Matrice 100",
                     "trajectoryType": self.parameters["trajectory_resolver"][
                         self.parameters["trajectory_type"]],
                     "safeAltitude": 50.0,
                     "maxAltitude": 120.0,
                     "initialSpeed": None,
                     "maxSpeed": None,
                     "failsafes": failsafe,
                     "checkAerodromeNfz": True,
                     "checkCustomNfz": True,
                     "segments": [],
                     "takeoffHeight": None,
                     }

        # check if route has home
        if home is not None:
            route = route[1:-2]  # get rid of home in route

        # transit in. point camera down
        lat, lng, alt, spd = route[0]
        alt = alt if bandAlt is not None else bandAlt
        pt = self.makePoint(lat, lng, bandAlt)
        routeJson["segments"].append(self.makeWaypoint(pt, spd,
                                                       tilt=90, camera=2))

        # take picture every 2 sec
        for lat, lng, alt, spd in route[1:-2]:
            pt = self.makePoint(lat, lng, alt)
            routeJson["segments"].append(self.makeWaypoint(pt, spd,  camera=2))
        # turn off camera
        lat, lng, alt, spd = route[-2]
        pt = self.makePoint(lat, lng, alt)
        routeJson["segments"].append(self.makeWaypoint(pt, spd))
        # ascend camera forward
        lat, lng, alt, spd = route[-1]
        alt = alt if bandAlt is not None else bandAlt
        pt = self.makePoint(lat, lng, bandAlt)
        routeJson["segments"].append(self.makeWaypoint(pt, spd, tilt=0))

        if home is not None:
            # take off
            # calculate offset point from lz
            offsetPt = self.offsetHome(home, route[1],
                                       self.parameters["offset_takeoff_dist"])
            lat, lng, alt, spd = offsetPt
            alt = alt if bandAlt is not None else bandAlt
            pt = self.makePoint(lat, lng, alt)
            routeJson["segments"].insert(0, self.makeWaypoint(pt, spd))

            # transfer out
            offsetPt = self.offsetHome(home, route[-1],
                                       self.parameters["offset_land_dist"])
            lat, lng, alt, spd = offsetPt
            alt = alt if bandAlt is not None else bandAlt
            pt = self.makePoint(lat, lng, alt)
            routeJson["segments"].append(self.makeWaypoint(pt, spd))
            # pre land
            if self.parameters["pre_land_alt"] is not None:
                pt = self.makePoint(lat, lng, self.parameters["pre_land_alt"])
                routeJson["segments"].append(self.makeWaypoint(pt, 4))

            # land if autoLand is True
            if self.autoland:
                pt = self.makePoint(lat, lng, 0.0)
                routeJson["segments"].append(self.makeLand(pt))

        return routeJson

    @staticmethod
    def makePoint(lat, lng, alt):
        pt = {"latitude": np.deg2rad(lat),
              "longitude": np.deg2rad(lng),
              "altitude": alt,
              "altitudeType": "AGL"
              }

        return pt

    @staticmethod
    def makeWaypoint(pt, spd, camera=None, tilt=None):
        # make paramter
        param = {"avoidObstacles": True,
                 "avoidTerrain": True,
                 "speed": spd,
                 "wpTurnType": "STRAIGHT",
                 "altitudeType": "AGL"
                 }
        # make waypoint
        waypt = {"type": "Waypoint",
                 "actions": [],
                 "point": pt,
                 "parameters": param
                 }
        if tilt is not None:
            action = {"type": "CameraControl",
                      "tilt": np.deg2rad(tilt),
                      "roll": 0.0,
                      "yaw": 0.0,
                      "zoomLevel": None
                      }

            waypt["actions"].append(action)

        if camera is not None:
            action = {"type": "CameraSeriesByTime",
                      "interval": camera,
                      "shotsNumber": None,
                      "startDelay": None,
                      "autoCalc": False
                      }

            waypt["actions"].append(action)
        return waypt

    @staticmethod
    def makeLand(pt):
        param = {"avoidObstacles": True,
                 "avoidTerrain": True,
                 "altitudeType": "AGL"
                 }
        # make waypoint
        waypt = {"type": "Landing",
                 "actions": [],
                 "point": pt,
                 "parameters": param
                 }
        return waypt

    @staticmethod
    def DJIprofile():
        profile = {"name": "DJI Matrice 100",
                   "vehicleType": "MULTICOPTER",
                   "modelKey": "dji_matrice_100",
                   "imageKey": "dji_matrice_100",
                   "platformCode": "DjiMatrice100",
                   "sealed": False,
                   "unremovable": True,
                   "primary": True,
                   "payloadProfiles": [],
                   "parameters": {"height": 0.25,
                                  "width": 0.65,
                                  "length": 0.65,
                                  "maxClimbRate": 6.0,
                                  "maxHorizontalSpeed": 15.0,
                                  "maxAltitude": 3000.0,
                                  "maxWaypoints": 99.0,
                                  "maxFlightTime": 1020.0,
                                  "windResistance": 10.0,
                                  "dryTakeoffWeight": 2.4,
                                  "maxTakeoffWeight": 3.6,
                                  "batteryWeight": 0.67,
                                  "chargedBatteryVoltage": 25.2,
                                  "dischargedBatteryVoltage": 21.0,
                                  "normalBatteryVoltage": 21.7,
                                  "lowBatteryVoltage": 21.5,
                                  "lowGpsSatellites": 7.0,
                                  "normalGpsSatellites": 9.0,
                                  "safeDistanceToTerrain": 5.0,
                                  "safeDistanceToObstacle": 20.0,
                                  "waypointAcceptanceRadius": 2.0,
                                  "fenceRadius": 3000.0,
                                  "lowTelemetryLevel": 50.0,
                                  "normalTelemetryLevel": 70.0,
                                  "defaultClimbRate": 2.0,
                                  "defaultDescentRate": 1.0,
                                  "glideSlope": None,
                                  "defaultHorizontalSpeed": 5.0,
                                  "landingGroundSpeed": None,
                                  "maxAltitudeAgl": 120.0,
                                  "landingFlareAltitude": None,
                                  "landingFlareTime": None,
                                  "minLandingPitch": None,
                                  "landingFlareDamp": None,
                                  "landingApproachAirspeed": None,
                                  "landingSpeedWeighting": None,
                                  "maxAutoFlightPitch": None,
                                  "maxPitch": None,
                                  "minThrottle": None,
                                  "landingSinkRate": None,
                                  "landingRangefinderEnabled": None,
                                  "minRangefinderDistance": None,
                                  "maxDescentRate": 6.0,
                                  "lowBatteryPowerLevel": 30.0,
                                  "normalBatteryPowerLevel": 40.0,
                                  "maxRangefinderDistance": None
                                  }
                   }
        return profile
