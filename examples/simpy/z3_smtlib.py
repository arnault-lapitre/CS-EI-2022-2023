from z3 import *
s = Solver()
s.from_string("(declare-const z_1 Real) (declare-const msg_ping_1 Int) (assert (and (> z_1 0) (and (> msg_ping_1 2) (< msg_ping_1 7) ) ))")
print(s)

print(s.check())
model = s.model()
print(model)

def mk_stim(name, sort):
    stim = sort(name)
    return stim

def mk_time(name):
    time = Real(name)
    return time

stim = mk_stim('msg_ping_1', Int)
time = mk_time('z_1')

print(model.evaluate(stim+42))
print(model.evaluate(time+5.5))
