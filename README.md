# WADL 
## Fighter Planner Software
### alpha 0.1

### requirements 
utm
shapely
z3-solver

## z3
z3 is a STM solver by microsoft 
you will need to follow the instructions on their page to install the binaries


## Usage
Extend the config class to your own configureation for some area. You will need to point it to a cvs file of boundary gps cords (lat long)

Configuration lets you set up where you want the agents to start from and the step size. You can also create smaller zones that tile the area.

After a configuration is made it can be passed the solver in main-sat