# WADL
![build](https://github.com/k2shah/wadl/workflows/build/badge.svg)
[![docs](https://readthedocs.org/projects/wadl/badge/?version=master)](https://wadl.readthedocs.io/en/master/?badge=master)
[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)

## Coverage Path Planner
<p float="center">
  <img src=docs/_static/overview/grid.png width=400 >
  <img src=docs/_static/overview/final.png width=400 >
</p>


WADL is a python package for planning surveys over large areas using one or more UAV (Unpersoned Aerial Vehicle). WADL take in a geofence and desired gird spacing and produces a series of routes to survey the area inside the geofence. 

The project was motivated by the need for efficient route planning for multi-robot systems. WADL was designed and used in a 2019-2020 survey of 
Adélie penguins over [Cape Crozier, Ross Island, Antarctica](https://goo.gl/maps/wrMTuMq5kyNxZafx8) If you are interested in the technical details please see our [paper](https://robotics.sciencemag.org/content/5/47/eabc3000)  To cite wadl please use the following citation:	
```
Shah, G. Ballard, A. Schmidt, M. Schwager, Multidrone aerial surveys of penguin colonies in Antarctica. Sci. Robot. 5, eabc3000 (2020). 
```
This work was supported by grant NSF grant 1834986 with logistical support provided by the [United States Antarctic Program](https://www.usap.gov/)

## Install
### pip
```
pip install wadl-planner
```
### source
```
git clone https://github.com/k2shah/wadl.git
pip install -r requirements.txt
```

## Usage
### Quick Start
```
from wadl.survey import Survey
survey = Survey()
survey.addTask(<path_to_geofence.csv>, step=100)
survey.plan()
```
Where ``step`` is the desired grid spacing.

See the [example](example/stanford.py) for a complete demonstration or the [tutorial](https://wadl.readthedocs.io/en/latest/tutorial.html) 

### Issues
For any suggestions or bugs please open an issue

### License
This software is licensed under [GNU GENERAL PUBLIC LICENSE verion 3](https://www.gnu.org/licenses/gpl-3.0)
