#!bin/bash/python3
import warnings as warn
import os
import sys
import time
# plot
import matplotlib.pyplot as plt
from osgeo import ogr
dateDir = "data/croz_geofence"
shapeFile = "croz_outer_bound.shp"

file = os.path.join(dateDir, shapeFile)
driver = ogr.GetDriverByName('ESRI Shapefile')
shapeData = driver.Open(file)
lyr = shapeData.GetLayer(0)

for feat in lyr:
    geom = feat.geometry()
    print(geom)
    r = geom.GetGeometryRef(0)
    x = [r.GetX(j) for j in range(r.GetPointCount())]
    y = [r.GetY(j) for j in range(r.GetPointCount())]

fig, ax = plt.subplots()
ax.plot(x, y)
plt.show()