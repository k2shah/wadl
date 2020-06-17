import utm
import geopy.distance
import numpy as np
import numpy.linalg as la
# import pyproj as pyproj

# pyproj.Proj(proj='utm', zone=32, ellps='WGS84')


c1 = (40.705823, -74.011071)
c2 = (38.968368, -77.387460)

d = geopy.distance.distance(c1, c2).km

print(d)

u1 = utm.from_latlon(*c1)
u2 = utm.from_latlon(*c2)

print(u1, u2)

u1c = np.array(u1[0:2])
u2c = np.array(u2[0:2])

dutm = la.norm(u1c-u2c)
print(dutm/1000)