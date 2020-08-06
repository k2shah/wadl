# gen
import time
# io
import json
import csv
import os.path as osp
import glob
# math
import numpy as np


class Mission(object):
    """creates a UGCS mission from a survey or directory of routes"""

    def __init__(self, autoLand=True):
        self.outDir = ""
        self.name = "mission"
        self.autoLand = autoLand
        self.data = {"version": {},
                     "payloadProfiles": [],
                     "vehicleProfiles": [self.DJIprofile()],
                     "mission": {},
                     "vehicles": []
                     }
        self.setVersion()

    def write(self):
        filename = osp.join(self.outDir, "mission.json")
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
                routes[name] = route.waypoints
        self.buildMission(routes)

    def fromDicr(self, srcDir):
        name = srcDir.split('\\')[-1]
        self.name = name.split('.csv')[0]
        self.outDir = srcDir
        routeFiles = glob.glob(osp.join(srcDir, "routes", "*.csv"))
        print(routeFiles)
        routes = {}
        for i, file in enumerate(routeFiles):
            with open(file, 'r') as csvfile:
                reader = csv.reader(csvfile, delimiter=',')
                route = [list(map(float, row[:4])) for row in reader]
                print(route)
                name = self.name + "_" + str(i)
                routes[name] = route
        self.buildMission(routes)

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
        # take off
        wp = r[0]
        pt = self.makePoint(*wp[:3])
        route["segments"].append(self.makeWaypoint(pt, wp[3]))
        # transit in. point camera down
        wp = r[1]
        pt = self.makePoint(*wp[:3])
        route["segments"].append(self.makeWaypoint(pt, wp[3], tilt=90))
        # take picture every 2 sec
        for wp in r[2:-4]:
            pt = self.makePoint(*wp[:3])
            route["segments"].append(self.makeWaypoint(pt, wp[3], camera=2))
        # ascend. turn off camera
        wp = r[-4]
        pt = self.makePoint(*wp[:3])
        route["segments"].append(self.makeWaypoint(pt, wp[3]))
        # transfer out. point camera forward
        wp = r[-3]
        pt = self.makePoint(*wp[:3])
        route["segments"].append(self.makeWaypoint(pt, wp[3], tilt=0))
        # decend to land location
        for wp in r[-2:]:
            pt = self.makePoint(*wp[:3])
            route["segments"].append(self.makeWaypoint(pt, wp[3]))

        # land if autoLand is True
        if self.autoLand:
            wp = r[-1]
            pt = self.makePoint(*wp[:2], 0.0)
            route["segments"].append(self.makeLand(pt))

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


if __name__ == '__main__':
    dirc = "C:\\Users\\kunal\\Documents\\surveys\\monoLake_20\\test\\Pancake_North_South_s20_r4"
    mission = Mission(autoLand=True)
    mission.fromDicr(dirc)
    mission.write()