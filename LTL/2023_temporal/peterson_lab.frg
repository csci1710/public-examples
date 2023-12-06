#lang forge

/* 
Peterson Lock model, used variously for lecture and lab in CSCI 1710
This is the complete version; ***EXERCISE*** annotations label places
to remove in a student-facing lab stencil. 

Written by Tim in Spring of 2023; Tim added some comments in December 2023. 

State:
  per process: boolean flag
  global: PID polite

Code of each process:
  while(true) { 
        [location: disinterested]
      this.flag := true;  // visible to other threads!
        [location: halfway]
      polite := this; 
        [location: waiting]
      while(other.flag == true && polite == this);    
        [location: in-cs] // "critical section"   
      this.flag := false;    
  }

Thus, a state in our model will have 2 boolean flags, 1 PID, and 2 locations.
*/

-- Tell Forge to run in Alloy 6 / Electrum mode: LTL, etc.
option problem_type temporal
-- Tell Forge that lasso traces found should be <= 10 states long
option max_tracelength 10

-- ***TODO***: allow process to delay interest indefinitely; this is more realistic, 
-- and key to modeling earlier, buggy versions of the algo. (If both processes contend 
-- endlessly, then a simpler locking algorithm works.)

--------------------------------------------------------------------------------------
-- Start by defining datatypes
--------------------------------------------------------------------------------------

abstract sig Location {}
one sig Disinterested, Halfway, Waiting, InCS extends Location {}

abstract sig Process {}
one sig ProcessA, ProcessB extends Process {}

-- I used "World" to represent a state. "var" fields may change over time
-- Some of these (certainly "loc") could have been fields of Process, but 
-- in this lecture context I like to group all the state together.
one sig World {
    var loc: func Process -> Location, -- total function 
    var flags: set Process,            -- set of processes
    var polite: lone Process           -- one process, or none
}

--------------------------------------------------------------------------------------
-- Now define the transition-system model of the algorithm: an initial-state
-- predicate and transition predicates.
--------------------------------------------------------------------------------------

-- Temporal mode is implicitly aware of time index, so "next_state init" means in 2nd state etc.
pred init {
    all p: Process | World.loc[p] = Disinterested -- begin at the start of the while loop
    no World.flags                                -- no process has its flag=true
    no World.polite                               -- no process has deferred
}

-- When defining transition predicates, it is useful to distinguish between whether
--   (a) the action is *enabled* for a given process; and
--   (b) the action is *taken* for a given process.

-- We have four system transitions:

---------------------------------------------------
-- Move from Disinterested to Halfway, raising flag
---------------------------------------------------
pred enabledRaise[p: Process] {
    World.loc[p] = Disinterested 
}
pred raise[p: Process] {
    enabledRaise[p]
    World.loc'[p] = Halfway
    World.flags' = World.flags + p
    World.polite' = World.polite
    all p2: Process - p | World.loc'[p2] = World.loc[p2]
}

---------------------------------------------------------------
-- Move from Halfway to Waiting, deferring to the other process
---------------------------------------------------------------
pred enabledNoYou[p: Process] {
    World.loc[p] = Halfway
}
pred noYou[p: Process] {
    enabledNoYou[p]
    World.loc'[p] = Waiting
    World.flags' = World.flags
    World.polite' = p
    all p2: Process - p | World.loc'[p2] = World.loc[p2]
}

--------------------------------------------------------------------------------------------------------
-- Move from Waiting to InCS, but only if only this flag is raised, or if the other process has deferred
--------------------------------------------------------------------------------------------------------
pred enabledEnter[p: Process] {
    World.loc[p] = Waiting 
    -- no other processes have their flag raised *OR* this process isn't the polite one
    (World.flags in p or World.polite != p)
}
pred enter[p: Process] {
    enabledEnter[p]
    World.loc'[p] = InCS    
    World.flags' = World.flags
    World.polite' = World.polite
    all p2: Process - p | World.loc'[p2] = World.loc[p2]
}

-------------------------------------------------------------------------
-- Exit the critical section, moving from InCS to Disinterested once more
-------------------------------------------------------------------------
pred enabledLeave[p: Process] {
    World.loc[p] = InCS    
}
pred leave[p: Process] {
    enabledLeave[p]
    World.loc'[p] = Disinterested    
    World.flags' = World.flags - p
    World.polite' = World.polite
    all p2: Process - p | World.loc'[p2] = World.loc[p2]
}

-- ...and one "meta" transition. LTL works with infinite traces, but Forge can
-- only find finite objects. Thus, the trace Forge finds must always have a loop 
-- back on itself. If there is no forward transition after a deadlock, deadlock 
-- traces will simply never be found by the solver. Hence this meta-transition.

-------------------------------------------------------------------------------
-- If no action is enabled for any process, continue the system state unchanged
-------------------------------------------------------------------------------
pred doNothing {
    -- GUARD (nothing else can happen)
    -- second way to allow disinterest is to uncomment this first line
    -- first way would be to have a special "remainDisinterested transition"
    not (some p: Process | enabledRaise[p])
    not (some p: Process | enabledNoYou[p]) 
    not (some p: Process | enabledEnter[p]) 
    not (some p: Process | enabledLeave[p])     
    -- ACTION
    flags' = flags
    loc' = loc
}

-- The name "transition" is reserved in Forge
-- Exercise: why is "some" safe here, given that "some" permits duplicates?
-- Answer: the way we wrote the framing conditions in the predicates above disallows duplicates.
pred step {
    some p: Process | 
        raise[p] or
        enter[p] or 
        leave[p] or 
        noYou[p] or
        doNothing 
}

-------------------------------------------------------------------------------

-- Reinforce the need for a loop by naming this predicate "lasso", not just "trace"
pred lasso {
    init            -- start in the initial state
    always step     -- in every state, take a forward transition
}

-- TN: I removed fairness here, because it's not needed under the way
-- the liveness property is currently phrased (only triggering an obligation 
-- once a process is *Waiting*), given that both processes are always interested. 

-------------------------------------------------------------------------------
-- Visualization
-- Show a valid lasso trace where no process remains disinterested forever.
-------------------------------------------------------------------------------

run {
  lasso  
  all p: Process | eventually World.loc[p] != Disinterested
}

-------------------------------------------------------------------------------
-- Validating the model
-------------------------------------------------------------------------------

test expect {
    vacuity: {lasso} is sat
    someoneCanGetIn: {
        lasso and 
        eventually {some p: Process | World.loc[p] = InCS }
    } is sat

  -- TN: removed the deadlock check, because its "true form" exists below 
  -- and because I'm working on reframing it in a better version of this model.
}

-------------------------------------------------------------------------------
-- Validating the model vs. the requirements
--  Two classic properties: mutual exclusion and non-starvation
-------------------------------------------------------------------------------

test expect {
    mutualExclusion: {
        lasso implies {
            always {
                -- one of few times I like using "lone"; recall it means "one or none"
                lone p: Process | World.loc[p] = InCS 
            }
        }
    } is theorem

    -- ***EXERCISE*** Start the below with "always eventually World.loc[p] = InCS". 
    --   Why does this fail?

    noStarvation: {
        lasso implies {
            all p: Process | {
                always {
                    -- ***DISCUSS*** beware saying "p in World.flags"; using loc is safer
                    --    Why? 
                    --    Answer: because if a process may be disinterested forever, but is 
                    --    interested (and gets access) one or more times, they will have their
                    --    flag raised while in the InCS state, incurring an obligation to access
                    --    the critical section *again*.
                    //p in World.flags =>
                    World.loc[p] = Waiting =>
                      eventually World.loc[p] = InCS
                }
            }
        }
    } is theorem

}


