import numpy as np
import numpy.linalg as la
import warnings as warn
# import numpy.random as rand


def l1(a, b):
    # returns the L1 norm of two vectors that are tuples
    return sum(abs((np.array(a) - np.array(b))))


def l2(a, b):
    # returns the L2 norm of two vectors that are tuples
    return la.norm(np.array(a) - np.array(b))


def rot2D(theta):
    # theta is in rads
    c = np.cos(theta)
    s = np.sin(theta)
    return np.array([[c, -s],
                     [s, c]])


def array2ListTuples(A):
    R, C = A.shape
    return [tuple(A[i, :]) for i in range(R)]


def sub2ind(cord, grid):
    # returns the linear index on the square index
    return cord[0] + grid[0]*cord[1]


def ind2sub(idx, grid):
    # returns the coordinate from the linear index
    return np.unravel_index(idx, grid, order="F")


def normalize(v):
    # reutns a normalized vector
    v = np.array(v)
    norm = la.norm(v)
    if norm < 10e-7:
        warn.warn("vector has near zero mag")
        return 0*v
    return v/norm

def calcDistFromLatLng(gps0, gps1):
    # calculates the distnce in meters of 2 lat/lng points
    e0, n0, _, _ = utm.from_latlon(*gps0)
    e1, n1, _, _ = utm.from_latlon(*gps1)
    return np.linalg.norm([e0-e1, n0-n1])
