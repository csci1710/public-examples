#lang forge
/*
  Modeling finite-trace LTL in Forge
  TN January 2023
*/

--open "ltlf_helpers.rkt"

-------------------------------------------------------
-- Formulas of LTLf 
--   leaving out R(elease) and X_w, since they can be desugared
--   via X, Not, and U. Similarly, leaving out implies and iff.
-------------------------------------------------------

abstract sig UOP, BOP {}
one sig Not, Next, Eventually, Always extends UOP {}
one sig And, Or, Until extends BOP {}

abstract sig Formula {}
sig Atom extends Formula {}
sig Unary extends Formula {
    uop: one UOP,
    sub: one Formula
}
sig Binary extends Formula {
    bop: one BOP,
    left: one Formula,
    right: one Formula
}

fun subformulas[fmla: Formula]: set Formula {
    fmla.^(sub + left + right)
}
pred wellformed_formulas {
    all f: Formula | f not in subformulas[f]
}

-------------------------------------------------------
-- Finite Traces
-------------------------------------------------------

sig State {
    truths: set Atom
}

-- Finite, possibly empty sequences of states
--   "first" should be uniquely derivable, if "next" is nonempty and linear
--   but having an explicit first field helps visualization
sig Trace {    
    first: lone State,
    next: pfunc State -> State
}

inst traces_optimizer {
    -- Don't use linear; linear implies _all states_ will be used.
    -- TODO: document this
    next is plinear
}

pred wellformed_traces {
    all t: Trace | {
        -- first is uniquely determined by next
        t.first = {s: t.next.State | s not in State.(t.next)}
        -- no cycles/repetition of state atoms (note two different "states" may share a truth table)
        no s: State | s in s.^(t.next)
    }
}

fun states[t: Trace]: set State {
    -- every pre-state and every post-state in the trace
    t.next.State + t.next[State]
}


// TODO: last -- should be a property that for every trace, last is unique

-------------------------------------------------------
-- Semantics
--   modeling this via a single table object, rather than 
--   a field on formulas, to make it easier to represent I,t |= F
-------------------------------------------------------

one sig Semantics {
    -- Trace at State makes Formula true
    table: set Trace -> State -> Formula
}

// This trick won't always work, but it does for tree-shaped data
pred semantics {
    all t: Trace, s: State, f: Formula | t->s->f in Semantics.table iff s in states[t] and {
        -- Atom case
        f in Atom and f in s.truths
        or
        -- Not case
        f.uop = Not and {
            t->s->(f.sub) not in Semantics.table           
        }
        or
        -- Eventually case
        f.uop = Eventually and {            
            some s2 : s.*(t.next) | t->s2->(f.sub) in Semantics.table            
        }
        or
        -- Always case
        f.uop = Always and {
            all s2 : s.*(t.next) | t->s2->(f.sub) in Semantics.table
        }
        or
        -- Next case
        f.uop = Next and {
            some t.next[s] and t->t.next[s]->(f.sub) in Semantics.table
        }
        or
        -- And case
        f.bop = And and {
            t->s->(f.left) in Semantics.table and
            t->s->(f.right) in Semantics.table
        }
        or
        -- Or case
        f.bop = Or and {
            t->s->(f.left) in Semantics.table or
            t->s->(f.right) in Semantics.table
        }
        or
        -- Until case (easier to express without lasso traces!)
        f.bop = Until and {
            some s2: s.*(t.next) | {
                t->s2->(f.left) in Semantics.table
                -- TODO: is this * or ^ in the first case?
                all smid: s.*(t.next) & s2.^~(t.next) | t->smid->(f.right) in Semantics.table
            }
        }
    }

}

-----------------------

--Example for visualization

--option verbose 5
// TODO: Trace sig wasn't visible until I moved this down?
run {
    wellformed_formulas
    wellformed_traces
    semantics
    some Binary
    some Unary
    some Trace
    some next
    some table
} for exactly 5 Formula for traces_optimizer

-- The lack of a term language is troublesome. If I want to write "GF(x1 or x2)" it isn't easy,
--   and getting the atom (likely using set comprehension) is different from quantifying for it.
-- Also, consider traces: we'd like to assert a certain trace exists and that it satisfies a certain fmla.
--   This "naturally" can be expressed as a `some` quantifier: some t: Trace, some f: Formula | ...
--   but that seems inflexible and verbose.

