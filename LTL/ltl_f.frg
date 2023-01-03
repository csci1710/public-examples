#lang forge
/*
  Modeling finite-trace LTL in Forge
  TN January 2023
*/

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
pred wellformed {
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
sig Trace {    
    next: pfunc State -> State
}

inst traces_optimizer {
    next is linear
}
fun first[t: Trace]: lone State {
    {s: t.next.State | s not in State.(t.next)}
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

pred semantics {
    all t: Trace, s: State, f: Formula | t->s->f in Semantics.table iff {
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
        -- Or case
        f.bop = Or and {
            t->s->(f.left) in Semantics.table or
            t->s->(f.right) in Semantics.table
        }
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

// TODO: Trace sig wasn't visible until I moved it down?
run {
    wellformed
} for exactly 5 Formula
