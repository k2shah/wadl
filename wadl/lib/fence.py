#!/usr/bin/python3
# io
from pathlib import Path
import csv
import logging
# math
import numpy as np
# gis
import utm
from shapely.geometry import Polygon
from fastkml import kml, geometry


class Fence(object):
    """Holds the gps cords of the boundary of the area given by a cvs file

    Args:
        file (str)

    """

    def __init__(self, file):
        self.file = Path(file)
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.INFO)
        # get name of area
        self.name = self.file.stem
        # parse file
        self.parseFile(file)
        # build polygon
        self.poly = Polygon(self.UTMCords)
        # find bounding box
        minx, miny, maxx, maxy = self.poly.bounds
        self.logger.info(f"extends in meters {maxx - minx} by {maxy - miny}")

    def parseFile(self, file):
        # parse file as CSV
        self.logger.info(f"Reading coordinate file {file}")
        # stores the gps cords, utm cords, and utm zones
        if file.suffix == "csv":
            CSVfile = file
        else:
            CSVfile = file.with_suffix(".csv")
        with open(CSVfile, 'r') as csvfile:
            data = [(line[1], line[2])
                    for line in csv.reader(csvfile, delimiter=',')]
        # toss 1st line and convert to float
        GPSData = [list(map(float, line)) for line in data[1:]]
        # convert to utm
        UTMData = [utm.from_latlon(cords[0], cords[1]) for cords in GPSData]
        # store coridinate information
        self.UTMZone = UTMData[0][2:]
        # print(self.UTMZone)
        self.UTMCords = np.array([[data[0], data[1]] for data in UTMData])
        self.GPSCords = np.array(GPSData)

    def plot(self, ax, color='m'):
        """Plots the geofence in UTM

        Args:
            ax (pyplot.axis): axis object from pyplot you want to draw on
            color ('str'): color string for the geofence.
                default 'm' (magenta).

        """
        # plots are always in utm
        ax.plot(*self.poly.exterior.xy, color=color)
        # place label somewhere
        minx, miny, maxx, maxy = self.poly.bounds
        placement = ((minx+maxx)/2, maxy)
        # ax.annotate(self.name, xy=placement)


class Areas(object):
    """Holds the gps cords of the set of areas given by a kml file

    Args:
        file (str): (lat,  lng)

    Returns
        Area: Container for a set of geofence objects

    """

    def __init__(self, file):
        self.file = file
        self.zones = []
        self.areas = []
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.INFO)
        self.name = self.file.stem
        self.parseFile(file)

    def __repr__(self):
        return self.areas.__repr__()

    def __iter__(self):
        return iter(self.areas)

    def __len__(self):
        return len(self.areas)

    def parseFile(self, file):
        with open(file, 'rt',) as f:
            doc = f.read()
        k = kml.KML()
        k.from_string(doc.encode('utf-8'))
        self.findPlacemarks(list(k.features()))
        self.logger.info(f"found {len(self.areas)} objects")

    def findPlacemarks(self, features):
        # parse features throughout the KML File
        for feature in features:
            if isinstance(feature, kml.Placemark):  # when there is no folder
                self.findGeometries(feature)
        for feature in features:
            if isinstance(feature, kml.Folder):
                self.findPlacemarks(list(feature.features()))
            if isinstance(feature, kml.Document):
                self.findPlacemarks(list(feature.features()))

    # parse geometry
    def findGeometries(self, placemark):
        if hasattr(placemark, "geometry"):
            if isinstance(placemark.geometry, geometry.LineString):
                self.logger.info("ignoring LineString")
            if isinstance(placemark.geometry, geometry.LinearRing):
                # print("found LinearRing")
                self.getUTMpoly(placemark.geometry)
            if isinstance(placemark.geometry, geometry.MultiPolygon):
                # print("found MultiPolygon")
                for poly in placemark.geometry:
                    self.getUTMpoly(poly.exterior)
            else:
                print(placemark.geometry, " object has no handler")

    def getUTMpoly(self, ring):
        UTM = [utm.from_latlon(cords[1], cords[0])
               for cords in ring.coords]
        # store coordinate information
        zone = UTM[0][2:]
        # print(self.UTMZone)
        coords = np.array([[data[0], data[1]] for data in UTM])
        self.zones.append(zone)
        self.areas.append(Polygon(coords))

    def toCSV(self):
        for i, (zone, area) in enumerate(zip(self.zones, self.areas)):
            cords = [utm.to_latlon(c[0], c[1], *zone)
                     for c in area.exterior.coords]
            outname = self.file.parent / Path(self.name+f"_{i}.csv")
            with open(outname, 'w', newline='') as csvfile:
                writer = csv.writer(csvfile, delimiter=',')
                writer.writerow(["FID", "lat", "lon"])
                for i, cord in enumerate(cords):
                    writer.writerow([i]+list(cord))

    def plot(self, ax, color='k'):
        """Plots the geofence in UTM

        Args:
            ax (pyplot.axis): axis object from pyplot you want to draw on

        """
        for area in self.areas:
            ax.plot(*area.exterior.xy, color=color)
