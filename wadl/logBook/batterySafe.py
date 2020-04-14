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


def calcDistFromLatLng(gps0, gps1):
    # calculates the distnce in meters of 2 lat/lng points
    e0, n0, _, _ = utm.from_latlon(*gps0)
    e1, n1, _, _ = utm.from_latlon(*gps1)
    return np.linalg.norm([e0-e1, n0-n1])

def distanceVBattery(bat, prog, mission, startIdx):
    bat = np.array(bat)
    prog = np.array(prog)
    basePt = mission[startIdx][1:3]
    # print(basePt)
    times = prog[:, 0]
    batInterp = np.interp(times, bat[:, 0], bat[:, 1])
    distances = [calcDistFromLatLng(basePt, mission[int(pt-1)][1:3])
                 for time, pt in prog]
    return np.array(batInterp), np.array(distances)


def main():
    logPath = os.getcwd()
    # get wildcard path missions/DATE/logs/*/LOGFILE_NAME.txt
    logPath = os.path.join(logPath, "missions/20-01-21/logs/*/*.txt")
    logFiles = glob.glob(logPath)
    logFiles.sort()
    print("Parseing Files")

    flights = []

    for logFile in logFiles:
        print(logFile)
        log = Log(logFile)
        flights.extend(log.flights)

    # throw away flight 1
    del flights[1]
    routeNums = [(int(flight.missionName.split("-")[0].strip('r')), i)
                 for i, flight in enumerate(flights)]
    routeNums.sort()
    print(routeNums)

    plt.style.use('fivethirtyeight')
    plt.rc('axes', titlesize=20)
    plt.rc('axes', labelsize=18)
    fig, ax = plt.subplots(figsize=(16, 9))
    plt.title('No Return Distance')
    fig.patch.set_facecolor('w')
    ax.set_facecolor('w')
    ax.set_xlim(95, 30)
    ax.set_xlabel("Battery Percent (%)")
    ax.set_ylim(0, 700)
    ax.set_ylabel("Distance From Start (m)")
    speed = 4  # speed m/s
    dRate = .11  # battery drain rate %/sec
    ax.plot([80, 30], [(80-30)/dRate*speed, 0], 'k:')
    starts = [2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2, 3]
    ends = [42, 41, 32, 42, 37, 35, 43, 36, 32, 40, 23]
    # for flightName, idx in routeNums:
    #     print(idx)
    #     flight = flights[idx]
    #     start = starts[idx]
    #     end = ends[idx]
    leggy = ['no return']
    for route, idx in routeNums:
        flight = flights[idx]
        start = starts[idx]
        end = ends[idx]
    # for flight, start, end in zip(flights, starts, ends):
        print(flight.missionName)
        leggy.append(flight.missionName.split("-")[0])
        bat, dists = distanceVBattery(flight.batteryLog,
                                      flight.missionProgress,
                                      flight.mission,
                                      start)
        # print(bat[start:end])
        # print(flight.missionProgress)
        # print(dists[start:end])
        if route > 6:
            style = "--"
        else:
            style = "-"
        ax.plot(bat[start:end], dists[start:end],
                linestyle=style)

    plt.legend(leggy)
    plt.savefig("safe.png", dpi=200, bbox='tight',
                facecolor=fig.get_facecolor(), edgecolor='w')
    plt.show()


if __name__ == '__main__':
    main()
