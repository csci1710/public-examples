#lang forge 
option backend smtlibtor

/*
  Bounded Collatz sequence in Forge, with and without SMT backend. This file
  uses the cvc4, theory-of-relations backend.
  
  Since this is meant to be a bounded trace, and we have no need of LTL, 
  we'll use Relational Forge rather than Temporal Forge here.

  This version creates a concrete trace of specific state constants, rather than
  using the usual `one sig Trace` approach, which performs poorly. 
  Here, we see the run terminate for len=10, but it is still worse performance than 
  the Pardinus backend (or using SMT directly) yields. The theory of relations is 
  not really helping here, but instead adds complexity. 
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

/** Traces over the transition-system model, with concrete constants  */
one sig S0, S1, S2, S3, S4, S5, S6, S7, S8, S9 extends State {}
pred delta[pre, post: State] {
    div2[pre, post] or mul3plus1[pre, post]
}
pred trace10 {
    -- Constrain the structure of the trace like 'is linear' would, using
    -- a specific a priori ordering. 
    init[S0]
    delta[S0, S1]
    delta[S1, S2]
    delta[S2, S3]
    delta[S3, S4]
    delta[S4, S5]
    delta[S5, S6]
    delta[S6, S7]
    delta[S7, S8]
    delta[S8, S9]
}

--run { trace10 } 

-- What if we had an _unsatisfiable_ version of this? It is still rather slower 
-- than the Pardinus version. 
test expect {
    unsat_10: { 
        trace10
        no s: State | s.x = 1
    } is unsat
} 
