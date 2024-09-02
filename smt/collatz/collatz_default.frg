#lang forge 

/*
  Bounded Collatz sequence in Forge, with and without SMT backend. This file
  uses the non-SMT, Pardinus backend. 
  
  Since this is meant to be a bounded trace, and we have no need of LTL, 
  we'll use Relational Forge rather than Temporal Forge here.

  The downside of using Pardinus is that integers will overflow according to the 
  bitwidth assigned, and that performance will degrade as the bitwidth increases. 
  The first 10 steps need to represent up to 64, which requires a bitwidth of 8,
  which yields the interval [-128, 127].

  Performance is still good, however, for this small trace-length = 10:
    Transl (ms): (time-translation 223); 
    Solving (ms): (time-solving 44)
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
    starting state and successor-state relations. Assume 
    'next is linear', which is similar to Alloy's 'open util/ordering[State]' */
one sig Trace {first: one State, next: pfunc State -> State}
pred trace { 
  no (Trace.first).~(Trace.next)
  init[Trace.first]
  all s: State | some Trace.next[s] implies {
    div2[s, Trace.next[s]] or
    mul3plus1[s, Trace.next[s]]
  }
}
run {trace} for 10 State, 8 Int for {next is linear}

