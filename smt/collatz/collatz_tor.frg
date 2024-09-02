#lang forge 
option backend smtlibtor

/*
  Bounded Collatz sequence in Forge, with and without SMT backend. This file
  uses the cvc4, theory-of-relations backend.
  
  Since this is meant to be a bounded trace, and we have no need of LTL, 
  we'll use Relational Forge rather than Temporal Forge here.

*/

/** Transition-system model */
sig State { x: one Int }
pred init[s: State] { s.x = 21 }
pred div2[pre,post: State] {
    remainder[pre.x, 2] = 0   -- GUARD
    post.x = divide[pre.x, 2] -- ACTION
}
pred mul3plus1[pre,post: State] {
    remainder[pre.x, 2] = 1             -- GUARD
    post.x = add[multiply[3, pre.x], 1] -- ACTION 
}

/** Traces over the transition-system model: 
    starting state and successor-state relations. However, we cannot use 'is linear'. */
one sig Trace {first: one State, next: pfunc State -> State}
pred trace { 
  no (Trace.first).~(Trace.next)
  init[Trace.first]
  all s: State | some Trace.next[s] implies {
    div2[s, Trace.next[s]] or
    mul3plus1[s, Trace.next[s]]
  }
}
run {
    -- SMT-SPECIFIC: Necessary for soundness without 'is linear'
    -- replaced with trace-structure constraints below
    one last_state: State | no Trace.next[last_state]
    no s: State | s in s.^(Trace.next)

    -- SMT-SPECIFIC: unbounded solver, disallow stopping after 1 state
    -- This performs poorly, even at #State = 2
    #State = 2

    trace
} 

