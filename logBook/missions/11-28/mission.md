# Mission 11-28
## Test Flights over C,P,N,M,L
### Mission Goal
Test 2 drones flying from the Hut to the colonies, taking off and landing at the hut. Testing the use of a "drone taxi" to recover drones form the landing field and reseting them at the take off spot with new batteries.

### Results 
2 drones (waddle 1/2) completed all tests. Waddle 2 encountered a "speedy" error, see notes

## Roles
### Pilots: KS, GB, PL
### VO: AS 
### Taxi: VM


## Tasks
- Test new home point/altitude settings.
- Test multi-drone observations and logistics
- Test auto land at the hut. 


## Flights
### Waddle 1 
#### Flight 1
- Pilot: KS
- Route: z3-0
- Path: Hut <> zone 3 (c/p)
![log](flight1.png)

### Waddle 2
#### Flight 1
- Pilot: AS
- Route: z0-0
- Path: Pats Peak -> zone 0 -> Hut
![log](flight2.png)

## Notes
Waddle 1 encounter a "speedy" error where it completed the route but at the transfer speed (14 m/s) not the survey speed (4 m/s). Logistics with the hut went well, resetting a drone requires a ~2.5 min imu initialization slows down the entire process.