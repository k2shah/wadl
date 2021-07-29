#!bin/bash/python3
# import warnings as warn
import csv
import logging
# gis
import utm
# math
import numpy as np
# lib
from wadl.lib.parameters import Parameters


class RouteParameters(Parameters):
    """Parameter container for setting route parameters

    Set parameters directly like how you would for a dictionary.
    ``routeParameters = RouteParameters``
    ``routeParameters["Parameter"] = value``

    Args:
        limit (float): route limit in seconds
        speed (float): route speed over coverage area in meters/seconds
        altitude (float): altitude above ground level of the coverage area in m
        xfer_speed (float): speed for transfer segments in m/s
        xfer_altitude (float): altitude for transfer segments in m
        xfer_ascend (float): ascend rate in m/s
        xfer_decend (float): descend rate in m/s
        land_altitude (float): altitude before landing

    """

    def __init__(self, default=True):
        super(RouteParameters, self).__init__(default)

    def setDefaults(self):
        self["limit"] = 13*60  # s
        self["speed"] = 4.0  # m/s
        self["prio_speed"] = 3.0  # m/s
        self["altitude"] = 35.0  # m
        self["xfer_speed"] = 12.0  # m/s
        self["xfer_altitude"] = 70.0  # m
        self["xfer_ascend"] = 5.  # m/s
        self["xfer_descend"] = 4.  # m/s
        self["land_altitude"] = 30  # m


class RouteSet(object):
    """container to for a set of routes

    Attributes:
        routes (list): list of routes

    Args:
        home (list): list of homes for the routes
        zone (tuple): tuple of UTM zone ("number", "N" or "S")
        routeParameters (RouteParameters): desired parameters for the routes.

    """

    def __init__(self, home, zone, routeParameters=None):
        # loggers
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)
        self.data = dict()

        self.home = home

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

    def __setitem__(self, key, value):
        self.data[key] = value

    def __getitem__(self, key):
        return self.data[key]

    def getLimit(self):
        # get the time limit
        return self.routeParameters['limit']

    def check(self, cords):
        """Builds the route from a UTM waypoint list and
        runs a series of checks to verify the route is viable.

        Args;
            cords (list): list of UTM waypoints

        Returns:
            None if any check fails;
            the Route otherwise

        """
        route = Route(cords, self.zone, self.home)
        route.build(self.routeParameters, priority=self.data["priority"])
        if route.check():
            return True, route
        else:
            return False, route

    def push(self, route):
        # push the route into the container
        self.routes.append(route)

    def write(self, pathDir):
        """writes the routes to a file

        Args:
            pathDir (str): location to save routes.

        """
        self.logger.info(f"writing routes to {pathDir}")
        for i, route in enumerate(self.routes):
            filename = pathDir / f"{i}.csv"
            route.write(filename)


class Route(object):
    """A route of points

    Attributes:
        UTMcords (list): list of points in UTM
        GPScords (list): list of points in GPS WGS84

    Args:
        cords (list): list of UTM waypoints of a route
        home (list): list of homes for the routes
        zone (tuple): tuple of UTM zone ("number", "N" or "S")

    """

    def __init__(self, cords, zone, home=None):
        # loggers
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)

        self.UTMcords = cords  # cords in UTM
        self.UTMZone = zone
        self.UTM2GPS(zone)  # set path in GPS (WGS 84)
        self.uncompleted = None
        self.lastNode = None
        self.linked = False
        self.group = -1
        if home is not None:
            self.setHome(home)  # set home pt (in GPS)
        else:
            self.home = home
        self.waypoints = []

        # path limits
        self.DJIWaypointLimit = 98

    def __repr__(self):
        return self.waypoints.__repr__()

    @staticmethod
    def DistGPS(gps0, gps1, alt0=0, alt1=0):
        # calculates the distance in meters of 2 lat/long points
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
        # resolve the home point
        self.homeDist = np.inf
        for h in home:
            (dist, i) = min([(self.DistGPS(np.array(h), np.array(pt)), i)
                             for i, pt in enumerate(self.GPScords)])
            if dist < self.homeDist:
                self.home = h
                idx = i
                self.homeDist = dist
        self.logger.debug(f"home set to {self.home}")

        # shift and wrap
        self.GPScords = self.GPScords[idx:] + self.GPScords[1:idx+1]
        # sync the utm
        self.GPS2UTM()

    def check(self):
        """ run a series of checks to see if this route is feasible

        Return:
            False if one of the length checks fail
            True otherwise
        """

        # check: under the waypoint limit
        self.length = 0.0
        self.ToF = 0.0
        passed = True
        if len(self.waypoints) > self.DJIWaypointLimit:
            passed = False
        # check: under the time limit
        if self.home is None:
            # split transfer and survey sections
            tran_in, ToF_in = self.calcLength(self.waypoints[:2])
            tran_out, ToF_out = self.calcLength(self.waypoints[-2:])
            self.len_tran = tran_in + tran_out
            self.ToF_tran = ToF_in + ToF_out
            # survey
            self.len_surv, self.ToF_surv = self.calcLength(
                self.waypoints[1:-2])
        else:
            # split transfer and survey sections
            tran_in, ToF_in = self.calcLength(self.waypoints[0:2])
            tran_out, ToF_out = self.calcLength(self.waypoints[-4:])
            self.len_tran = tran_in + tran_out
            self.ToF_tran = ToF_in + ToF_out
            # survey
            self.len_surv, self.ToF_surv = self.calcLength(
                self.waypoints[2:-4])
        self.length = self.len_tran + self.len_surv
        self.ToF = self.ToF_tran + self.ToF_surv
        if self.ToF > self.limit:
            passed = False
        return passed

    def calcLength(self, waypoints):
        # return the length and ToF of the segment
        length = 0
        ToF = 0
        if len(waypoints) < 2:
            self.logger.debug("waypoint segment does not have at least 2 pts")
            return 0, 0
        for wp, nxt in zip(waypoints, waypoints[1:]):
            dist = self.DistGPS(wp[0:2], nxt[0:2], wp[2], nxt[2])
            length += dist
            ToF += dist/wp[3]
        return length, ToF

    def build(self, routeParameters, priority=None):
        # build the path
        # unpack parameters
        self.limit = routeParameters["limit"]
        spd = routeParameters["speed"]
        priSpd = routeParameters["prio_speed"]
        alt = routeParameters["altitude"]
        xferSpd = routeParameters["xfer_speed"]
        xferAlt = routeParameters["xfer_altitude"]
        xferAsc = routeParameters["xfer_ascend"]
        xferDes = routeParameters["xfer_descend"]
        landALt = routeParameters["land_altitude"]

        if priority is None:
            priority = set()

        # take off
        if self.home is not None:
            Hlat, Hlng = self.home
            self.waypoints.append([Hlat, Hlng, xferAlt, xferSpd])
            # get higher above first point, point camera down
        lat, lng = self.GPScords[0]
        self.waypoints.append([lat, lng, xferAlt, xferDes])
        # push each waypoint
        for gpsPt, utmPt in zip(self.GPScords[:-1], self.UTMcords[:-1]):
            lat, lng = gpsPt
            roundedUTM = tuple(map(int, utmPt))
            s = priSpd if roundedUTM in priority else spd
            self.waypoints.append([lat, lng, alt, s])
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

    def plot(self, ax, color='b'):
        # path
        cords = np.array(self.UTMcords)
        ax.plot(cords[:, 0], cords[:, 1], color=color)
        # start and end
        if len(cords) > 3:
            ax.scatter(cords[0, 0], cords[0, 1], color=color, marker='^')
            ax.scatter(cords[-2, 0], cords[-2, 1], color=color, marker='s')
        if self.home is not None:
            # plot the home point as a 'o'
            HomeUTMx, HomeUTMy = utm.from_latlon(*self.home)[0:2]
            ax.scatter(HomeUTMx, HomeUTMy, color=color, marker='o')
            ax.plot([HomeUTMx, cords[0, 0]], [HomeUTMy, cords[0, 1]],
                    color=color, linestyle="--")

    def write(self, filename):
        # writes the waypoints as a text file
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
