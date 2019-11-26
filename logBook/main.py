#!/usr/bin/python3

# std
import os
import sys
import glob
# math
import numpy as np
# plots
import matplotlib.pyplot as plt
# lib
from lib.log import Log, Flight


def main(filePath):
    logFiles = glob.glob(os.path.join(filePath, "*.txt*"))
    print("Parseing Files")
    for logFile in logFiles:
        print(logFile)
        log = Log(logFile)
        print(log.header["name"])
        for i, flight in enumerate(log.flights):
            print('flight: {:d}'.format(i))
            print(flight)
            fig, ax = plt.subplots()
            plt.title('flight: {:d}'.format(i))
            flight.plotBattery(ax)
            plt.draw()
            plt.pause(.000001)
        plt.show()


if __name__ == '__main__':
    if len(sys.argv) == 2:
        main(sys.argv[1])
    else:
        print('Usage:')
        print(' {} <log data directory>'.format(sys.argv[0]))
    sys.exit(0)
#     # file = 'logs/2.18.98_2019_11_21_12_16.txt'
#     file = 'logs/2.18.98_2019_11_25_15_01.txt'
#     log = Log(file)

#     for i, flight in enumerate(log.flights):
#         print(i)
#         fig, ax = plt.subplots()
#         plt.title('flight')
#         flight.plotBattery(ax)
#         print(flight.startTime)
#         print(flight.duration)
#         print(flight.routeEnd-flight.routeStart)
#         print(flight.mission)
#         plt.draw()
#         plt.pause(.000001)
#     plt.show()
