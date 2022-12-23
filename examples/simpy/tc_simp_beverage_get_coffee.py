from z3 import *
import simpy.rt
from time import perf_counter
from time import perf_counter_ns
from inputimeout import inputimeout

def mk_var(typed_variables):
    stim = {}
    for v in typed_variables:
        stim[v] = typed_variables[v](v)        
    return stim

def tc_01(env):
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
    formula_stim = """(declare-const z_1 Real) (declare-const c_1 Int) (declare-const m_1 Int)
                    (assert 
                            (and (> z_1 0) 
                                (and (= c_1 2) (> m_1 0)
                                ) 
                            )
                    )
        """
    s.from_string(formula_stim)
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
    #get integer part of covert_stim_dur-sol_dur
    remaining_stim_dur = int(covert_stim_dur-sol_dur) 

    print('remaining_stim_dur (in seconds)', remaining_stim_dur)
   
    if remaining_stim_dur < 0:
        print('TRACE : Inc_sol no time submit stim  (time to submit stim - solving time) = %.2f (in seconds)' %remaining_stim_dur)
    else: 
        yield env.timeout(covert_stim_dur)
        #buverage!(c, m) with c: choice among 1 or 2, m: money amount
        print('\nTRACE : stimulation time (in seconds)', env.now)
        print('TRACE : stimulation buverage!', stim_val)
    
    #instrumentation to get obs duration
    try:
        #WaitMax = 5 seconds maximum waiting time for observations
        # n.b, method inputimeout() takes timeout in seconds
        WaitMax = 10 
        start = perf_counter() #use instead perf_counter_ns() ns for nano seconds
        obs = inputimeout(prompt="beverage?\n", timeout=WaitMax)
        end = perf_counter()
        obs_dur = end - start #get in nano seconds covert into milli seconds
        print('Duration to observation time unit: %.2f (in seconds)' % obs_dur)
        print('Observation :', obs)
        
        formula_obs = "(assert true)"
        formula_obs = """(declare-const z_1 Real) (declare-const z_2 Real) (declare-const c_1 Int)
                    (assert 
                            (and (> z_1 0) 
                                (and (= c_1 2) 
                                    (and (> z_2 0) 
                                        (and (> z_2 2) (< z_2 10)
                                        )
                                    )
                                )
                            )
                    )
        """
        s_obs = Solver()
        #To-Do add obs_dur (and obs) to formula (z2 = obs_dur) s.t int(obs_dur*1000)
        s_obs.from_string(formula_obs)
        print(s_obs) 
        vdt_sat = s_obs.check()
        print(vdt_sat)     

        if vdt_sat == sat:
            model = s_obs.model()
            print(model)    
            if obs == 'coffee':
                print('TRACE : Pass test success')
            elif obs == 'abort':
                print('TRACE : Inc_out specfied output outside test purpose')
            else :
                print('TRACE : Fail test failure')
        else:
            print('TRACE : Fail test failure unsat ot timeout solver')
            
        # Catch the timeout error
    except Exception:
        
        # Declare the timeout statement
        print('TRACE : Inc_obs no observation timeout on MaxWait = %.2f (in seconds)' % WaitMax)
    

#creation of a real-time (rt) environment env to which processes will be added 
#duration of one simulation step: 0.001 seconds
# n.b, The step() method will raise a RuntimeError 
#   if a time step took too long to compute. 
#   This behaviour can be disabled by setting *strict* to False.
env = simpy.rt.RealtimeEnvironment(factor=0.001, strict=False)

#add rt process "car" to env 
env.process(tc_01(env))
env.run(until=25000)






