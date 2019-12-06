#!bin/bash/python3

# std
import os
import sys
import time
import warnings
# math
import numpy as np
# plots
import matplotlib.pyplot as plt


class Log(object):
    """container for the entire flight log of one session of UgCS"""

    def __init__(self, file):
        self.file = file  # log file
        # [year, mon, day]
        self.flightDate = file.split("_")[1:4]
        # header info
        self.header = {'name': None,
                       'firmwareVer': None,
                       'type': "DJIM100"}
        self.flights = []  # list of fights
        self.parseFile()  # parse the log

    def parseFile(self):

        # flags
        parseMission = False
        missionName = None
        parseFlight = False
        # tags
        # headers
        nameTag = 'AircraftName = '
        verTag = 'FirmwareVersion = '

        # mission
        misisonStartTag = 'DJI_M100, simulator=OFF'
        missionNameTag = ".ugcs'"
        missionWPTag = "WP #"
        missionEndTag = 'Mission Upload - Result - SUCCESS'

        # trajectory
        flightStartTag_asit = '''onFlightMode change: GPS_ATTI
                                 ->  ASSISTED_TAKEOFF'''
        flightStartTag_auto = 'onFlightMode change: GPS_ATTI -> AUTO_TAKEOFF'
        autoFlightStartTag = 'Toast message: Route started'
        batteryTag = 'Battery updated:'
        autoFlightEndTag = 'Toast message: Route ended'
        autoFlightCancelTag = 'Toast message: Route canceled'
        flightEndTag = 'TAKEOFF_POSITION_UPDATED as landed'

        with open(self.file) as f:
            for line in f:
                ls = line.split(" : ")
                if len(ls) < 2:
                    # finds a mission being uploaded
                    if missionNameTag in line and missionName is None:
                        missionName = line.split()[1]
                        missionName = missionName.split(".")[0]
                        missionName = missionName.strip("'")
                    if misisonStartTag in line:
                        WPbuffer = []  # holds waypoints until they are flown
                        # buffer is overwritten when new route is uploaded
                        parseMission = True
                        continue
                    if parseMission:
                        if missionWPTag in line:
                            data = line.split(missionWPTag)[1].split(', ')
                            # get heading
                            heading = data[0].split("heading=")[1]
                            heading = int(heading.split('(')[0])
                            # parse alt and lat long
                            cords = data[1].split(" ")
                            alt = self.getNum(cords[0], 'alt=m')
                            lat = self.getNum(cords[1], 'lat=')
                            lon = self.getNum(cords[2], 'lon=')
                            WPbuffer.append([heading, lat, lon, alt])

                else:  # if the split finds a DJI event
                    if parseMission:
                        if missionEndTag in ls[1]:
                            parseMission = False
                    if parseFlight:
                        if batteryTag in ls[1]:
                            percent, volt, temperature = self.getBattery(ls[1])
                            time = ls[0].split(" ")[0]
                            flight.addBatteryLog(
                                time, percent, volt, temperature)

                        elif autoFlightStartTag in ls[1]:
                            time = ls[0].split(" ")[0]
                            flight.setRouteStart(time)
                            # add the mission to the flight
                            flight.setMission(WPbuffer, missionName)
                            missionName = None
                        elif autoFlightEndTag in ls[1] or autoFlightCancelTag in ls[1]:
                            time = ls[0].split(" ")[0]
                            flight.setRouteEnd(time)

                        elif flightEndTag in ls[1]:
                            parseFlight = False
                            time = ls[0].split(" ")[0]
                            flight.setDuration(time)
                            self.flights.append(flight)

                    # FIND THE start of a flight
                    elif flightStartTag_auto in ls[1] or flightStartTag_asit in ls[1]:
                        parseFlight = True
                        time = ls[0].split(" ")[0]
                        # split time to [HH, MM, SS.dd]
                        time = time.split(":")
                        flight = Flight(time, self.flightDate)

                    # Parse for Header #
                    # uav name
                    elif not self.header['name']:
                        if nameTag in ls[1]:
                            self.header['name'] = ls[1].split(nameTag)[
                                1].strip()

                    # firmware ver
                    elif not self.header['firmwareVer']:
                        if verTag in ls[1]:
                            self.header['firmwareVer'] = ls[1].split(verTag)[
                                1].strip()

    def getNum(self, val, extra):
        # parses the val from "alt=XXm" or "lat=YY"
        val = val.strip(extra)
        return float(val)

    def getBattery(self, batteryString):
        #  assumes the battery string is the part after the : in the log e.g.
        #  Battery{exists=true, currentVoltage, currentCurrent,
        #   remainPowerPercent, smartBattery temperature}.
        batteryString = batteryString.strip("Battery updated: Battery{")
        batteryString = batteryString.split("}")[0]
        batteryString = batteryString.split(", ")
        volt = self.getNum(batteryString[1], 'currentVoltage=')/1000
        percent = self.getNum(batteryString[3], 'remainPowerPercent=')
        temperature = self.getNum(batteryString[5], 'temperature=')
        return percent, volt, temperature


class Flight(object):
    """container for a single flight"""

    def __init__(self, startTime, flightDate):
        self.startTime = list(map(float, startTime))  # time of start
        self.flightDate = flightDate
        self.duration = None  # duration in (sec) of flight
        self.routeStart = 0  # start of auto route
        self.routeEnd = 0  # end of auto route
        self.batteryLog = []  # history of the battery
        self.missionName = None
        self.mission = []  # planned mission uploaded
        self.trajectory = []  # flown trajectory
        self.isManual = False  # manual flight

    def __repr__(self):
        # prints the information for the mission
        # start time
        printStr = "flight started at: "
        printStr += "{:2.0f}:{:02.0f}:{:02.0f}\n".format(*self.startTime)
        # duration
        printStr += "flight duration: {:2.3f}m\n".format(self.duration/60.)
        if len(self.mission) == 0:
            printStr += "no mission for this flight\n\n"
            self.isManual = True
        else:
            # mission time
            printStr += "====Mission===="
            printStr += "route: {:s}\n".format(self.missionName)
            printStr += "autonomous duration: {:2.3f}m\n".format(
                         (self.routeEnd-self.routeStart)/60.)
            printStr += "lat\t\tlng\t\talt\n"
            # mission
            for pt in self.mission:
                printStr += "{:2.5f}\t{:2.5f}\t{:-2.3f}\n".format(
                             pt[1], pt[2], pt[3])
        # battery
        if len(self.batteryLog) > 0:
            printStr += "====Battery====\n"
            printStr += "start:\t{:2.4f}%\t{:2.4f}C\n".format(
                         self.batteryLog[0][1], self.batteryLog[0][3])
            printStr += "end:\t{:2.4f}%\t{:2.4f}C\n".format(
                         self.batteryLog[-1][1], self.batteryLog[-1][3])

        return printStr

    def setMission(self, mission, missionName):
        # sets the mission
        self.mission = mission
        self.missionName = missionName

    def addBatteryLog(self, time, percent, voltage, temperature):
        time = self.getRelativeTime(time)
        self.batteryLog.append([time,
                                percent,
                                voltage,
                                temperature])

    def getRelativeTime(self, time):
        # time is "hh:mm:ss.dd"
        time = time.split(':')
        timeDiff = [float(t) - float(s) for t, s in zip(time, self.startTime)]
        return 3600*timeDiff[0] + 60*timeDiff[1] + timeDiff[2]

    def setRouteStart(self, time):
        self.routeStart = self.getRelativeTime(time)

    def setRouteEnd(self, time):
        self.routeEnd = self.getRelativeTime(time)

    def setDuration(self, time):
        self.duration = self.getRelativeTime(time)

    def plotBattery(self, ax):
        batLog = np.array(self.batteryLog)
        # plot battery and temp
        ax.plot(batLog[:, 0]/60., batLog[:, 1], 'k')  # bat %
        ax.plot(batLog[:, 0]/60., batLog[:, 3], 'r')  # temp
        # add route break
        ax.vlines(self.routeStart/60., 0, 100, 'c')
        ax.vlines(self.routeEnd/60., 0, 100, 'm')

        # plotted for style
        ax.set_xlabel('flight time (m)')
        ax.legend(["percent %", "temp (C)", 'route start', 'route end']),


if __name__ == '__main__':
    # file = 'logs/2.18.98_2019_11_21_12_16.txt'
    file = '../logs/2.18.98_2019_11_25_15_01.txt'
    log = Log(file)

    for i, flight in enumerate(log.flights):
        print(i)
        fig, ax = plt.subplots()
        plt.title('flight')
        flight.plotBattery(ax)
        print(flight.startTime)
        print(flight.duration)
        print(flight.routeEnd-flight.routeStart)
        print(flight.mission)
        plt.draw()
        plt.pause(.000001)
    plt.show()
