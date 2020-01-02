#!/usr/bin/python3

# std
import os
import sys
import glob
import time
# math
import numpy as np
import utm
# plots
import matplotlib.pyplot as plt
# lib
from lib.log import Log, Flight


class FlightStat(object):
    """docstring for FlightStat
    Holds the data for a single units's total flight time and count"""

    def __init__(self, name):
        # store the name of the units
        self.name = name
        self.flightTime = 0.0  # flight time in minutes
        self.flightCount = 0  # number of flights
        # dict of flights. k: epoch time of flight, v: flight
        self.flights = dict()

    def addFights(self, log):
        for flight in log.flights:
            # check if flight actually as a duration
            if flight.duration:
                flightTime = time.struct_time((flight.flightDate[0],
                                               flight.flightDate[1],
                                               flight.flightDate[2],
                                               int(flight.startTime[0]),
                                               int(flight.startTime[1]),
                                               int(flight.startTime[2]),
                                               1, 1, 1))
                self.flights[flightTime] = flight
                self.flightCount += 1
                self.flightTime += flight.duration


def main():
    logPath = os.getcwd()
    # get wildcard path missions/DATE/logs/*/LOGFILE_NAME.txt
    logPath = os.path.join(logPath, "missions/*/logs/*/*.txt")
    logFiles = glob.glob(logPath)
    logFiles.sort()
    print("Parseing Files")

    flightStats = dict()

    for logFile in logFiles:
        print(logFile)
        log = Log(logFile)
        waddleName = log.header["name"]
        if waddleName is None:
            continue
        waddleName = cleanName(waddleName)
        try:
            flightStats[waddleName].addFights(log)
        except KeyError as e:
            # add a new unit
            flightStats[waddleName] = FlightStat(waddleName)
            flightStats[waddleName].addFights(log)

    showStats(flightStats)
    writeStatsMD(flightStats)
    writeStatsCSV(flightStats)


def showStats(flightStats):
    waddleName = list(flightStats.keys())
    waddleName.sort()
    print("name\t\ttime (min)\tcount")
    print("-"*30)
    for waddle in waddleName:
        print("{:s}\t\t{:3.2f} min\t{:d}".format(
            waddle,
            flightStats[waddle].flightTime/60,
            flightStats[waddle].flightCount))


def writeStatsMD(flightStats):
    waddleName = list(flightStats.keys())
    waddleName.sort()
    fileName = "stats/stats.md"
    with open(fileName, "w+") as f:
        f.write("# Waddle Flight Stats\n")
        nowTime = time.localtime()
        f.write('### complied on {:d}/{:d}/{:d} {:d}:{:d}:{:d}\n'.format(
            nowTime.tm_year,
            nowTime.tm_mon,
            nowTime.tm_mday,
            nowTime.tm_hour,
            nowTime.tm_min,
            nowTime.tm_sec,))
        # list of (etime of flight, waddle_ID)
        flightKeys = []
        # write data for each unit
        f.write("\n# Flights\n")
        for waddle in waddleName:
            # aggregate data
            f.write("\n{:s}: {:d} flights. {:3.2f} mins\n".format(
                waddle,
                flightStats[waddle].flightCount,
                flightStats[waddle].flightTime/60))
            # aggreate all times and id's
            for key in flightStats[waddle].flights.keys():
                flightKeys.append((key, waddle))

        # Write the stats by date
        flightKeys.sort()
        # Track last date
        lastDate = None
        for i, (flightKey, waddle) in enumerate(flightKeys):
            flight = flightStats[waddle].flights[flightKey]
            # f.write("- {:d}".format(i))

            # date information
            dateStr = "{:s}/{:s}/{:s}".format(
                      *flight.flightDate)
            if dateStr != lastDate:
                f.write("\n## " + dateStr + "\n")
                lastDate = dateStr
                flightCounter = 1

            if not flight.isManual:
                # route information
                f.write("{:d}. {:s} route: {:s}\n".format(
                        flightCounter,
                        waddle,
                        flight.missionName))
                f.write("\t- start: {:2.0f}:{:02.0f}:{:02.0f}\n".format(
                    *flight.startTime))
                durationMin = int(flight.duration / 60)
                durationSec = flight.duration % 60
                f.write("\t- duration: {:d}:{:02.0f} min\n".format(
                        durationMin,
                        durationSec))
                # battery information
                f.write("\t- battery start:\t{:02.0f}%\t{:2.2f}C\n".format(
                         flight.batteryLog[0][1],
                         flight.batteryLog[0][3]))
                f.write("\t- battery end:\t  {:02.0f}%\t{:2.2f}C\n".format(
                         flight.batteryLog[-1][1],
                         flight.batteryLog[-1][3]))

                # distance information
                mission = np.array(flight.mission)
                # f.write("\t- average altitude (AGL):\t{:2.2f}m\n".format(
                #          np.mean(mission[:, 3])))
                f.write("\t- maximum altitude (AGL):\t{:2.2f}m\n".format(
                         np.max(mission[:, 3])))

                # get 1st lat/lng pt
                startPt = (mission[0][1], mission[0][2])
                # calculate horizontal distance
                horzDistances = [calcDistFromLatLng(
                                 startPt,
                                 (pt[1], pt[2]))
                                 for pt in mission]
                f.write("\t- maximum horizontal distance:\t{:2.2f}m\n".format(
                         np.max(horzDistances)))

            flightCounter += 1
    f.close()


def writeStatsCSV(flightStats):
    waddleName = list(flightStats.keys())
    waddleName.sort()
    fileName = "stats/stats.csv"
    with open(fileName, "w+") as f:
        f.write("waddle ID,")
        f.write("date,")
        f.write("route name,")
        f.write("start time,")
        f.write("duration,")
        f.write("battery percent start (%),")
        f.write("battery temp start (C),")
        f.write("battery percent end (%),")
        f.write("battery temp end (C),")
        f.write("maximum altitude (m),")
        f.write("maximum horizontal distance (m)\n")
        for waddle in waddleName:
            # Track last date
            lastDate = None
            flightKeys = list(flightStats[waddle].flights.keys())
            flightKeys.sort()
            for i, flightKey in enumerate(flightKeys):
                flight = flightStats[waddle].flights[flightKey]
                f.write("{:s},".format(waddle))
                # date information
                f.write("{:s}/{:s}/{:s},".format(
                         *flight.flightDate))

                if not flight.isManual:
                    # route information
                    f.write("{:s},".format(flight.missionName))
                    f.write("{:2.0f}:{:02.0f}:{:02.0f},".format(
                             *flight.startTime))
                    durationMin = int(flight.duration / 60)
                    durationSec = flight.duration % 60
                    f.write("{:d}:{:02.0f},".format(
                            durationMin,
                            durationSec))
                    # battery information
                    f.write("{:02.0f},{:2.2f},".format(
                             flight.batteryLog[0][1],
                             flight.batteryLog[0][3]))
                    f.write("{:02.0f},{:2.2f},".format(
                             flight.batteryLog[-1][1],
                             flight.batteryLog[-1][3]))

                    # distance information
                    mission = np.array(flight.mission)
                    # f.write("\t- average altitude (AGL):\t{:2.2f}m\n".format(
                    #          np.mean(mission[:, 3])))
                    f.write("{:2.2f},".format(
                             np.max(mission[:, 3])))

                    # get 1st lat/lng pt
                    startPt = (mission[0][1], mission[0][2])
                    # calculate horizontal distance
                    horzDistances = [calcDistFromLatLng(
                                     startPt,
                                     (pt[1], pt[2]))
                                     for pt in mission]
                    f.write("{:2.2f}\n".format(
                             np.max(horzDistances)))

    f.close()


def cleanName(name):
    # get rid of a space in the unit's name
    nameSplit = name.split(" ")
    if len(nameSplit) > 1:
        name = nameSplit[0]+nameSplit[1]
    return name


def calcDistFromLatLng(gps0, gps1):
    # calculates the distnce in meters of 2 lat/lng points
    e0, n0, _, _ = utm.from_latlon(*gps0)
    e1, n1, _, _ = utm.from_latlon(*gps1)
    return np.linalg.norm([e0-e1, n0-n1])


if __name__ == '__main__':
    main()
    sys.exit(0)
