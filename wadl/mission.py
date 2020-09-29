# gen
import time
import warnings
# io
import json
import csv
from pathlib import Path
# gis
import utm
# math
import numpy as np
# lib
from .lib.parameters import Parameters


class MissionParameters(Parameters):
    """docstring for MissionParamters"""

    def __init__(self, default=True):
        super(MissionParameters, self).__init__(default)

    def setDefaults(self):
        self["autoLand"] = True
        self["offsetTakeoff"] = True
        self["offsetLand"] = False
        self["nBands"] = 1
        self["bandStart"] = 50
        self["bandStep"] = 10
        self["bandRadialOffset"] = 10


class Mission(object):
    """creates a UGCS mission from a survey or directory of routes"""

    def __init__(self, missionParamters=None):
        self.outDir = ""
        self.name = "mission"

        if missionParamters is None:
            self.paramters = MissionParameters()
        else:
            self.parameters = missionParamters

        self.data = {"version": {},
                     "payloadProfiles": [],
                     "vehicleProfiles": [self.DJIprofile()],
                     "mission": {},
                     "vehicles": []
                     }

        self.autoLand = self.parameters["autoLand"]
        # altitude bands for vertical seperation
        self.nBands = self.parameters["nBands"]
        bandStep = self.parameters["bandStep"]
        bandStart = self.parameters["bandStart"]
        self.bandOffset = self.parameters["bandRadialOffset"]
        self.bands = bandStart +\
            np.linspace(0, (self.nBands-1)*bandStep, self.nBands)

        self.setVersion()

    def write(self):
        filename = self.outDir / "mission.json"
        with filename.open('w') as f:
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

    def fromSurvey(self, survey, rewrite=True):
        # match the name and output directory
        self.name = survey.name
        self.outDir = survey.outDir
        routes = []
        # get all the routes in the survey (from each maze)
        for task, maze in survey.tasks.items():
            if maze.routeSet.home is None:
                warnings.warn("routeSet has no Home. Disabling route offsets")
                self.parameters["offsetTakeoff"] = False
                self.parameters["offsetLand"] = False
                routes.append(route)
        self.buildMission(routes, rewrite)

    def fromDirc(self, srcDir):
        name = srcDir.split('\\')[-1]
        self.name = name.split('.csv')[0]
        self.outDir = Path(srcDir)
        routeFiles = Path(srcDir, "routes").glob("*.csv")
        print(routeFiles)
        routes = []
        for i, file in enumerate(routeFiles):
            with file.open('r') as csvfile:
                reader = csv.reader(csvfile, delimiter=',')
                route = [list(map(float, row[:4])) for row in reader]
                print(route)
                # name = self.name + "_" + str(i)
                routes.append(route)
        self.buildMission(routes)

    def buildMission(self, routes, rewrite):
        mission = {"name": self.name,
                   "description": None,
                   "creationTime": int(time.time())}

        self.data["mission"] = mission
        # sort the routes angluarly
        routes.sort(key=self.headingAngle)
        if rewrite:
            path = Path(self.outDir, "routes")
            path.mkdir(exist_ok=True)
            for i, route in enumerate(routes):
                filename = self.outDir / "routes" / f"{i}.csv"
                route.write(filename)

        self.data["mission"]["routes"] = self.buildRoutes(routes)

    @staticmethod
    def headingAngle(route):
        # returns the inital heading angle of a route
        wp = route.waypoints
        angle = np.arctan2(wp[1][1]-wp[0][1],
                           wp[1][0]-wp[0][0])
        return (angle + 2 * np.pi) % (2 * np.pi)

    def offsetStart(self, route):
        # returns a pt 10m from the 1st pt on the route along the 1st segment
        pt0 = route[0]
        pt1 = route[1]
        pt0_utm = utm.from_latlon(*pt0[:2])
        pt1_utm = utm.from_latlon(*pt1[:2])

        zone_utm = pt0_utm[2:]
        vec = np.array(pt1_utm[:2])-np.array(pt0_utm[:2])

        # normalize and scale
        vec = vec/np.linalg.norm(vec) * self.bandOffset
        offsetPt = np.array(pt0_utm[:2]) + vec
        lat, lng = utm.to_latlon(*offsetPt, *zone_utm)
        return [lat, lng, *pt0[2:]]

    def buildRoutes(self, routes):
        routeList = []
        RoutePerSector = int(len(routes)/self.nBands) + 1
        for i, r in enumerate(routes):
            bandIdx = int(i/RoutePerSector)
            transferAlt = self.bands[bandIdx]
            name = f"{bandIdx}_{int(transferAlt)}_{i}"
            routeList.append(self.makeRoute(name, r.waypoints, transferAlt))
        return routeList

    # helper functions to build the waypoint lists
    def makeRoute(self, name, r, bandAlt=0):
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
        if self.parameters["offsetTakeoff"]:
            # calculate offset point from lz
            offsetPt = self.offsetStart(r)
            lat, lng, alt, spd = offsetPt
        else:
            lat, lng, alt, spd = r[0]
        pt = self.makePoint(lat, lng, bandAlt)
        route["segments"].append(self.makeWaypoint(pt, spd))
        # transit in. point camera down
        lat, lng, alt, spd = r[1]
        pt = self.makePoint(lat, lng, bandAlt)
        route["segments"].append(self.makeWaypoint(pt, spd,
                                                   tilt=90, camera=2))
        # take picture every 2 sec
        for lat, lng, alt, spd in r[2:-4]:
            pt = self.makePoint(lat, lng, alt)
            route["segments"].append(self.makeWaypoint(pt, spd,  camera=2))
        # turn off camera
        lat, lng, alt, spd = r[-4]
        pt = self.makePoint(lat, lng, alt)
        route["segments"].append(self.makeWaypoint(pt, spd))
        # ascend camera forward
        lat, lng, alt, spd = r[-3]
        pt = self.makePoint(lat, lng, bandAlt)
        route["segments"].append(self.makeWaypoint(pt, spd, tilt=0))
        # transfer out
        lat, lng, alt, spd = r[-2]
        pt = self.makePoint(lat, lng, bandAlt)
        route["segments"].append(self.makeWaypoint(pt, spd))
        # pre land
        if self.parameters["offsetLand"]:
            # calculate offset point from lz
            offsetPt = self.offsetStart(r)
            lat, lng, alt, spd = offsetPt
        else:
            lat, lng, alt, spd = r[-1]
        pt = self.makePoint(lat, lng, alt)
        route["segments"].append(self.makeWaypoint(pt, spd))

        # land if autoLand is True
        if self.autoLand:
            pt = self.makePoint(lat, lng, 0.0)
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
