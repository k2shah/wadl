#!bin/bash/python3
# import warnings as warn
import csv
import logging
# gis
import utm
# math
import numpy as np
import numpy.linalg as la
# lib
from .parameters import Parameters


class RouteParameters(Parameters):
    """docstring for routeParameters"""

    def __init__(self, default=True):
        super(RouteParameters, self).__init__(default)

    def setDefaults(self):
        self["limit"] = 13*60  # s
        self["speed"] = 4.0  # m/s
        self["altitude"] = 35.0  # m
        self["xfer_speed"] = 12.0  # m/s
        self["xfer_altitude"] = 70.0  # m
        self["xfer_ascend"] = 5.  # m/s
        self["xfer_descend"] = 4.  # m/s
        self["land_altitude"] = 30  # m


class RouteSet(object):
    """docstring for RouteSet"""

    def __init__(self, home, zone, routeParameters=None):
        # loggers
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)

        self.home = home
        self.multiHome = True if isinstance(home, tuple) else False

        self.zone = zone  # store the UTM zone
        self.routes = []

        # set the parameters
        if routeParameters is None:
            self.routeParameters = RouteParameters()
        else:
            self.routeParameters = routeParameters

    def __len__(self):
        return len(self.routes)

    def __iter__(self):
        return iter(self.routes)

    def check(self, cords):
        # builds the route from a UTM waypoint list
        # runs a series of checks to verify the route is viable
        # returns None if any check fails; the Route otherwise
        route = Route(cords, self.zone, self.home)
        route.build(self.routeParameters)
        if route.check():
            return route
        else:
            return None

    def push(self, route):
        # push the route into the container
        self.routes.append(route)

    def write(self, pathDir):
        self.logger.info(f"\tgenerated {len(self.routes)} routes")
        for i, route in enumerate(self.routes):
            filename = pathDir / f"{i}.csv"
            route.write(filename)
            self.logger.info(f"\t\troute {i}:\t"
                             f"{route.length:2.2f} m \t{route.ToF:2.2f} sec ")


class Route(object):
    """docstring for Route"""

    def __init__(self, cords, zone, home):
        # loggers
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)

        self.UTMcords = cords  # cords in UTM
        self.UTMZone = zone
        self.UTM2GPS(zone)  # set path in GPS (WGS 84)
        if home is None:
            self.home = None
        else:
            self.setHome(home)  # set home pt (in GPS)
        self.waypoints = []

        # path limits
        self.DJIWaypointLimit = 98

    @staticmethod
    def DistGPS(gps0, gps1, alt0=0, alt1=0):
        # calculates the distnce in meters of 2 lat/lng points
        e0, n0, _, _ = utm.from_latlon(*gps0)
        e1, n1, _, _ = utm.from_latlon(*gps1)
        return np.linalg.norm([e0-e1, n0-n1, alt0-alt1])

    def UTM2GPS(self, zone):
        # converts all the UTM cords to GPS
        self.GPScords = [utm.to_latlon(*cord, *zone) for cord in self.UTMcords]

    def GPS2UTM(self):
        # converts all the GPS cords to UTM
        self.UTMcords = [utm.from_latlon(*cord)[0:2] for cord in self.GPScords]

    def setHome(self, home):
        # reolve the home point
        if isinstance(home, list):
            # home: (lat, long)
            # finds the cloest pt on the route to the home
            (dist, idx) = min([(la.norm(np.array(home)-np.array(pt)), i)
                               for i, pt in enumerate(self.GPScords)])
            # sets the route home at the home pt
            self.home = np.array(home)
        elif isinstance(home, tuple):
            homeDist = np.inf
            for h in home:
                (dist, i) = min([(la.norm(np.array(h)-np.array(pt)), i)
                                for i, pt in enumerate(self.GPScords)])
                if dist < homeDist:
                    self.home = np.array(h)
                    idx = i
                    homeDist = dist
        self.logger.debug(f"home set to {self.home}")

        # shift and wrap
        self.GPScords = self.GPScords[idx:] + self.GPScords[1:idx+1]
        # sync the utm
        self.GPS2UTM()

    def check(self):
        # attempts to merge the segment into the path
        # returns False if one of the length checks fail

        # check: under the waypoint limit
        if len(self.waypoints) > self.DJIWaypointLimit:
            return False
        # check: under the time limit
        self.ToF = 0  # time of flight
        self.length = 0
        for wp, nxt in zip(self.waypoints, self.waypoints[1:]):
            dist = self.DistGPS(wp[0:2], nxt[0:2], wp[2], nxt[2])
            self.length += dist
            self.ToF += dist/wp[3]

        if self.ToF > self.limit:
            return False
        return True

    def build(self, routeParameters):
        # build the path

        # unpack parameters
        self.limit = routeParameters["limit"]
        spd = routeParameters["speed"]
        alt = routeParameters["altitude"]
        xferSpd = routeParameters["xfer_speed"]
        xferAlt = routeParameters["xfer_altitude"]
        xferAsc = routeParameters["xfer_ascend"]
        xferDes = routeParameters["xfer_descend"]
        landALt = routeParameters["land_altitude"]

        # take off
        if self.home is not None:
            Hlat, Hlng = self.home
            self.waypoints.append([Hlat, Hlng, xferAlt, xferSpd])
            # get higher above frist point, point camera down
        lat, lng = self.GPScords[0]
        self.waypoints.append([lat, lng, xferAlt, xferDes])
        # push each waypoint
        for lat, lng in self.GPScords[:-1]:
            self.waypoints.append([lat, lng, alt, spd])
        lat, lng = self.GPScords[-1]
        # last point to ascend to transfer
        self.waypoints.append([lat, lng, alt, xferAsc])
        # get higher above last point, point camera fwd
        self.waypoints.append([lat, lng, xferAlt, xferSpd])
        if self.home is not None:
            # return home
            self.waypoints.append([Hlat, Hlng, xferAlt, xferDes])
            # land
            self.waypoints.append([Hlat, Hlng, landALt, xferDes])

    def __len__(self):
        # number of waypoints in path
        return len(self.UTMcords)

    # def parseFile(self):
    #     pathFiles = glob.glob(os.path.join(self.pathDir, "routes/*"))
    #     for file in pathFiles:
    #         self.cords = dict()
    #         # print(file)
    #         with open(file) as csvfile:
    #             for line in csv.reader(csvfile, delimiter=','):
    #                 if line[2] != '50':
    #                     continue
    #                 cords = (line[0], line[1])
    #                 if cords in self.keyPoints:
    #                     continue
    #                 try:
    #                     self.cords[cords] += 1
    #                 except KeyError as e:
    #                     self.cords[cords] = 1
    #             try:
    #                 routeEff = self.calcEff()
    #                 print(file, ": ", routeEff)
    #                 self.writeEff(file, routeEff)
    #             except ZeroDivisionError as e:
    #                 print("invalid file: {:s}".format(file))

    # def calcEff(self):
    #     nPts = 0
    #     nPaths = 0
    #     for keys in self.cords:
    #         nPaths += self.cords[keys]
    #         nPts += 1
    #     return nPts/nPaths

    # def writeEff(self, routeFile, routeEff):
    #     infoFile = os.path.join(self.pathDir, "info.txt")
    #     if os.path.exists(infoFile):
    #         writeMode = 'a'
    #     else:
    #         writeMode = 'w'
    #     with open(infoFile, writeMode) as f:
    #         routeName = routeFile.split('/')[-1]
    #         f.write("\n{:s}: {:2.4f}".format(
    #                 routeName,
    #                 routeEff))

    def plot(self, ax, color='b'):
        # path
        cords = np.array(self.UTMcords)
        ax.plot(cords[:, 0], cords[:, 1], color=color)
        # start and end
        ax.scatter(cords[0, 0], cords[0, 1], color=color, marker='^')
        ax.scatter(cords[-2, 0], cords[-2, 1], color=color, marker='s')
        if self.home is not None:
            # plot the home point as a 'o'
            HomeUTMx, HomeUTMy = utm.from_latlon(*self.home)[0:2]
            ax.scatter(HomeUTMx, HomeUTMy, color=color, marker='o')
            ax.plot([HomeUTMx, cords[0, 0]], [HomeUTMy, cords[0, 1]],
                    color=color, linestyle="--")

    def write(self, filename):
        # writes the waypoints as a txt file
        with filename.open('w', newline='') as csvfile:
            writer = csv.writer(csvfile, delimiter=',')
            # take off
            row = self.waypoints[0] + ["FALSE", "", "", ""]
            writer.writerow(row)
            # transfer in
            row = self.waypoints[1] + ["FALSE", "", "", "90.0"]
            writer.writerow(row)
            for wp in self.waypoints[2:-3]:
                row = wp + ["FALSE", "", "", ""]
                writer.writerow(row)
            # transfer out
            row = self.waypoints[-3] + ["FALSE", "", "", "0.0"]
            writer.writerow(row)
            # land
            row = self.waypoints[-2] + ["FALSE", "", "", ""]
            writer.writerow(row)
            row = self.waypoints[-1] + ["FALSE", "", "", ""]
            writer.writerow(row)
