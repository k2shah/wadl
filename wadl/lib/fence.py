#!/usr/bin/python3
import csv
import logging
# math
import numpy as np
import pandas as pd 
# gis
import utm
from shapely.geometry import Polygon
#XML parser->   
from bs4 import BeautifulSoup


class Fence(object):
    """Holds the gps cords of the boundary of the area given by a cvs file

    Args:
        file (str): (lat,  lng)

    """

    def __init__(self, file):
        self.file = file
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.INFO)
        # get name of area
        self.name = file.name.split('.csv')[0]
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
        ax.annotate(self.name, xy=placement)


class Areas(object):
    """Holds the gps cords of the set of areas given by a kml file

    Args:
        file (str): (lat,  lng)

    Returns
        Area: Container for a set of geofence objects

    """

    def __init__(self, file):
        self.areas = dict()
        print(file)
        self.parseFile(file)

    def parseFile(self, file):
        # parse the cords from the KML file
        nameTag = "<name>"
        cordsTag = "<coordinates>"
        with open(file, 'r') as f:
            for line in f:
                if nameTag in line:
                    name = self.stripXML(line)
                    # print(name)
                    self.areas[name] = []
                if cordsTag in line:
                    cords = f.readline()

                    cords = cords.strip()
                    cords = cords.split(" ")
                    self.areas[name].append(
                        np.array([list(map(float, c.split((","))))
                                  for c in cords]))
                    # print(self.areas[name])

    def stripXML(self, string):
        # strips the "<>" and "/<>" from a string
        temp = string.split('>')[1]
        return temp.split('<')[0]

    def plot(self, ax):
        """Plots the geofence in UTM

        Args:
            ax (pyplot.axis): axis object from pyplot you want to draw on

        """
        for areaKey in self.areas:
            for ring in self.areas[areaKey]:
                ax.plot(ring[:, 0], ring[:, 1], 'k')

    # function to export CSV from KML
    def KML2CSV(self, file):
        with open(file, 'r') as f: 
            data = f.read()
        XML_data = BeautifulSoup(data, "xml") 

        #extracting the coordinates from the XML file
        jargon = XML_data.find_all('coordinates')

        #extracting the file name found in the KML tag <name> under <Placemark>.
        name = XML_data.find_all('Placemark')[0].text.split('\n',-1)[1] + ".csv"
        
        #jargon is a single string element list->
        #extracting the coordinate text data from this jargon
        latlong = [i.text for i in jargon]

        #converting it to list with latitide and longitude strings
        #by spliiting the string
        latlong2 = latlong[0].split('\n',-1)

        #adding the lattitudes and longitudes to a dictionary file
        coordinates ={'fid':[],'lat':[],'lon':[]}
        i=1
        for coord in latlong2:
            # here 20 is taken because "lat,long" string length = 21 which is the minimum req length
            #removing any leading or trailing whitespaces
            coord = coord.strip()
            if len(coord) >2:
                #splitting the string again into lattitude, longitude and grabage
                coord = coord.split(',',-1)
                #print(coord)
                coordinates['fid'].append(i) # index
                i = i+1
                coordinates['lat'].append(float(coord[0]))#storing the lattitde into the dictionary
                coordinates['lon'].append(float(coord[1]))#storing the logitude into the dictionary
        
        #converting to dataframe to save as a CSV.
        df = pd.DataFrame(coordinates) 
        
        #saving as a csv
        pr = df.to_csv(name,encoding='utf-8' ,index=False)
