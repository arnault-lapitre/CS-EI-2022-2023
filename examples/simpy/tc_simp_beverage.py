from z3 import *
import simpy.rt
from time import perf_counter

def mk_var(typed_variables):
    stim = {}
    for v in typed_variables:
        stim[v] = typed_variables[v](v)        
    return stim

def tc_coffee(env):
    print('time (in seconds)', env.now)

    #test case variable creation
    typed_vars = {'c_1':Int, 'm_1':Int}
    stim = mk_var(typed_vars)
    typed_durs = {'z_1':Real, 'z_2':Real}
    time = mk_var(typed_durs)

    #get couple (stim_val, dur_val) by constraint solving
    # stim_val is the stimulus to apply
    # dur_val is the time to apply the stimulus
    s = Solver()
    s.from_string("(declare-const z_1 Real) (declare-const c_1 Int) (assert (and (> z_1 0) (= c_1 2)) )")
    print(s)
    
    #instrumentation to get solving duration
    start = perf_counter()
    print(s.check()) 
    end = perf_counter()
    sol_dur = end - start
    print('Duration of solving time unit: %.2f (in seconds)' % sol_dur)
    
    model = s.model()
    print(model)
    stim_val = model.evaluate(stim['c_1'])
    print('stim_val ->', stim_val)
    stim_dur = model.evaluate(time['z_1'])
    print('stim_dur ->', stim_dur)
    
    covert_stim_dur = stim_dur.as_long()*1000
    if (sol_dur >= 1000): 
        remaining_stim_dur = covert_stim_dur-sol_dur
    else:
        remaining_stim_dur = covert_stim_dur
    print('remaining_stim_dur (in seconds)', remaining_stim_dur)
   
    if remaining_stim_dur < 0:
        print('inconc_solving')
    else: 
        yield env.timeout(covert_stim_dur)
        #buverage!(c, m) with c: choice among 1 or 2, m: money amount
        print('\nTRACE : stimulation time (in seconds)', env.now)
        print('TRACE : stimulation buverage!', stim_val)
    

#creation of a real-time (rt) environment env to which processes will be added 
#duration of one simulation time unit: 0.001 seconds
env = simpy.rt.RealtimeEnvironment(factor=0.001)

#add rt process "car" to env 
env.process(tc_coffee(env))
env.run(until=15000)






