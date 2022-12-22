import simpy.rt

# definition of process "car" 
def car(env):
    while True:
        print('Start parking at', env.now)
        parking_duration = 5
        yield env.timeout(parking_duration)
        print('Start driving at', env.now)
        trip_duration = 2
        yield env.timeout(trip_duration)

#creation of a real-time (rt) environment env to which processes will be added 
#duration of one simulation time unit: 0.10 seconds
env = simpy.rt.RealtimeEnvironment(factor=0.1)

#add rt process "car" to env 
env.process(car(env))
env.run(until=15)