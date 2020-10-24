.. wadl documentation master file, created by
   sphinx-quickstart on Sun Oct 18 15:40:47 2020.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Coverage Path Planner
========================

``wadl`` is a python package for planning surveys over large areas using one or more UAV (Unpiloted Aerial Vehicle). WADL take in a geofence and desired gird spacing and produces a series of routes to survey the area inside the geofence. 

``wadl`` is licensed under GPL v3. More information can be found in the :ref:`license` section.

Motivation
----------

The project was motivated by the need for efficient route planning for multi-robot systems. WADL was designed and used in a 2019-2020 survey of Adélie penguins over `Cape Crozier`_, Ross Island, Antarctica.

.. _Cape Crozier: https://goo.gl/maps/wrMTuMq5kyNxZafx8) 

If you are interested in the technical details please see our paper <> 


Citing
------

To cite wadl please use the following publication:

.. only:: html

   `PDF <.pdf>`

================================

.. toctree::
   :maxdepth: 2
   :caption: Contents:
   
   install
   tutorial
   reference/index
   license


Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
