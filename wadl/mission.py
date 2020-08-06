import json
import os.path as osp
import numpy as np
import time


class Mission(object):
    """creates a UGCS mission from a survey or directory of routes"""

    def __init__(self):
        self.outDir = ""
        self.name = "mission"
        self.data = {"version": {},
                     "payloadProfiles": [],
                     "vehicleProfiles": [self.DJIprofile()],
                     "mission": {},
                     "vehicles": []
                     }
        self.setVersion()

    def write(self):
        filename = osp.join(self.outDir, self.name+".json")
        with open(filename, 'w') as f:
            json.dump(self.data, f,
                      indent=2, separators=(',', ': '))

    def setVersion(self, major=3, minor=6, build=225):
        # set the version of UGSC
        version = {"major": major,
                   "minor": minor,
                   "build": build,
                   "component": "DATABASE"
                   }
        self.data["version"] = version

    def fromSurvey(self, survey):
        # match the name and output directory
        self.name = survey.name
        self.outDir = survey.outDir
        routes = {}
        # get all the routes in the survey
        for task, maze in survey.tasks.items():
            print(maze.name)
            for i, route in enumerate(maze.routeSet.routes):
                name = maze.name + "_" + str(i)
                routes[name] = route
        self.buildMission(routes)

    def fromDicr(self, dir):
        pass

    def buildMission(self, routes):
        mission = {"name": self.name,
                   "description": None,
                   "creationTime": int(time.time())}

        self.data["mission"] = mission
        self.data["mission"]["routes"] = self.buildRoutes(routes)

    def buildRoutes(self, routes):
        routeList = []
        for name, route in routes.items():
            routeList.append(self.makeRoute(name, route))
        return routeList

    # helper functions to build the waypoint lists
    def makeRoute(self, name, r):
        failsafe = {"rcLost": "GO_HOME",
                    "gpsLost": None,
                    "lowBattery": None,
                    "datalinkLost": None
                    }
        route = {"name": name,
                 "creationTime": int(time.time()),
                 "scheduledTime": None,
                 "startDelay": None,
                 "vehicleProfile": "DJI Matrice 100",
                 "trajectoryType": "STRAIGHT",
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
        for wp in r.waypoints:
            pt = self.makePoint(*wp[:3])
            route["segments"].append(self.makeWaypoint(pt, wp[3]))

        return route

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
