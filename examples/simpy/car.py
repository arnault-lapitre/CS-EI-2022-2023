import simpy

# definition of process "car" 
def car(id, env):
    while True:
        print('car', id, ': Start parking at', env.now)
        parking_duration = 5
        yield env.timeout(parking_duration)
        print('car', id, ': Start driving at', env.now)
        trip_duration = 2
        yield env.timeout(trip_duration)


def car_slow(id, env):
    while True:
        print('car', id, ': Start parking at', env.now)
        parking_duration = 8
        yield env.timeout(parking_duration)
        print('car', id, ': Start driving at', env.now)
        trip_duration = 4
        yield env.timeout(trip_duration)

#creation of an environment env to which processes will be added 
env = simpy.Environment()

#add processes "car" to env 
env.process(car(1, env))
env.process(car(2, env))
env.process(car_slow(3, env))
env.run(until=15)
