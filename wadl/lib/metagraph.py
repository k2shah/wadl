#!bin/bash/python3

import os
from copy import copy, deepcopy
# import sys
import time
# math
import numpy as np
# plot
import matplotlib.pyplot as plt
# lib
try:
    from .utils import *
    from .config import Config
except (SystemError, ImportError):
    from utils import *
    from config import Config


class Metagraph(object):
    """docstring for Metagraph
    a graph like object that holds a pair of (n,v)
    this graph represents a space filling graph
    the purpose of this object is to condense n by n grids to a single node
    to reduce the graph size while still retaining the connective properties"""
    def __init__(self, nodes, con, worldSize):
        # graph objects
        self.nodes = []
        self.con = dict()
        # base graph objects
        # baseNodes map: i-> s where i is the linear index, s is a world node
        self.baseNodes = nodes
        # con is a map i -> [] where [] is the connected indices
        self.baseCon = con
        # world size of the space filled, used to get gird cord in the "world"
        self.worldSize = worldSize
        # dict of the meta nodes, value is the reduced cluster
        self.metaNodes = dict()

    def __repr__(self):
        printStr = ''
        for n in self.nodes:
            try:
                self.metaNodes[n]
                printStr += 'm-'
            except KeyError as e:
                pass
            printStr += str(n) + ": " + str(self.con[n]) + "\n"
        return printStr

    def reduce(self, size, verbose=False):
        # finds size by size sub grids in the graph to generate a reduced graph
        # the set of nodes that a metaNode corresponds to
        # n -> -cl(n/2) ->  fl(n/2)
        start = int(size/2)
        walk = []
        for dx in range(-start, start+1):
            for dy in range(-start, start+1):
                if dx == 0 and dy == 0:
                    continue
                walk.append((dx, dy))

        # dict of all nodes, reduced nodes point to the parent
        self.reducedNodes = dict()

        # find meta nodes
        tic = time.time()
        nodeSet = set(self.baseNodes)
        for i in range(len(self.baseNodes)):
            node = self.baseNodes[i]
            if node not in nodeSet:
                continue
            x, y = ind2sub(node, self.worldSize)
            # skip edge points
            if x == 0 or x == self.worldSize[0]-1:
                continue
            if y == 0 or y == self.worldSize[1]-1:
                continue
            cluster = [sub2ind((x+dx, y+dy), self.worldSize) for dx, dy in walk]
            if nodeSet.issuperset(set(cluster)):
                # add to nodes
                self.nodes.append(node)
                # add to meta nodes
                self.metaNodes[node] = cluster
                # point to self
                self.reducedNodes[node] = node
                # point reduced nodes to the parent node
                for ln in cluster:
                    self.reducedNodes[ln] = node
                nodeSet.difference_update(set(cluster))
        # rebuild graph
        # rebuild nodes
        for i, node in enumerate(self.baseNodes):
            # ignore if reduced node
            try:
                self.reducedNodes[node]
            except KeyError as e:
                # add to graph if normal node (not meta or reduced)
                self.nodes.append(node)
                # self reduction (auto reduction)
                self.reducedNodes[node] = node
        # rebuild con
        for i, node in enumerate(self.baseNodes):
            # check if meta node
            con = set()
            try:
                cluster = self.metaNodes[node]
                # for each node in the reduced cluster
                for ln in cluster:
                    # for each node connected
                    # add the
                    for nn in self.baseCon[ln]:
                        if nn in self.baseNodes:
                            con.add((self.reducedNodes[nn]))
            except KeyError as e:
                # for a normal node
                for nn in self.baseCon[node]:
                    if nn in self.baseNodes:
                        con.add((self.reducedNodes[nn]))
            # remove self connections
            con.discard(node)
            self.con[node] = list(con)
        # sort the nodes because it's probably all mixed up
        self.nodes.sort()

        if verbose:
            print("reduction time {:2.3f}".format(time.time()-tic))
            print("reduced {:d} to {:d} ({:d})".format(
                  len(self.baseNodes),
                  len(self.nodes),
                  len(self.baseNodes)-len(self.nodes)))
            print("with {:d} meta nodes".format(len(self.metaNodes)))

    def plot(self, ax, world):
        for node in self.nodes:
            ax.scatter(*world[:, node],
                       color='b', marker='s')
            for adj in self.con[node]:
                ax.plot([world[0, node], world[0, adj]],
                        [world[1, node], world[1, adj]],
                        color='b')


if __name__ == '__main__':
    size = (10, 15)
    config = Config(typ='small', size=size)
    metagraph = Metagraph(config.stateSpace,
                          config.con,
                          config.worldSize)
    metagraph.reduce(3, verbose=True)
    print(metagraph)

    fig, ax = plt.subplots()
    config.plot(ax)
    metagraph.plot(ax, config.world)
    plt.show()
