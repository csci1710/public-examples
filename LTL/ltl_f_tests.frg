#lang forge

open "ltl_f.frg"

one sig GFPORQ, FPORQ extends Unary {}
one sig PORQ extends Binary {}
one sig P, Q extends Atom {}
one sig TraceA, TraceB extends Trace {}
one sig S_none, S_p, S_q, S_pq extends State {}

pred wellformed_example_gfporq {
    GFPORQ.uop = Always
    GFPORQ.sub = FPORQ
    FPORQ.uop = Eventually
    FPORQ.sub = PORQ
    PORQ.bop = Or
    PORQ.left = P
    PORQ.right = Q

    no S_none.truths
    S_p.truths = P
    S_q.truths = Q
    S_pq.truths = P + Q

    TraceA.first = S_none
    TraceA.next = S_none -> S_p + 
                  S_p -> S_q + 
                  S_q -> S_pq
    TraceB.first = S_p
    TraceB.next = S_p -> S_q + 
                  S_q -> S_pq
}

// option logtranslation 2
// option coregranularity 2
// option solver MiniSatProver
// option core_minimization rce
// option verbose 5

test expect {
    test_gfporq_sat: {
        wellformed_formulas
        wellformed_traces
        semantics
        wellformed_example_gfporq
    } for 5 Formula for traces_optimizer is sat
    
    -- Note this will fail for "6 Formula", since new fmlas might also be satisfied by TraceA/TraceB
    test_gfporq_theorem: {
        {
            wellformed_formulas
            wellformed_traces
            semantics
            wellformed_example_gfporq
        } implies {            
            Semantics.table[TraceA][S_none] = GFPORQ + FPORQ 
            Semantics.table[TraceA][S_p] = GFPORQ + FPORQ + PORQ + P
            Semantics.table[TraceA][S_q] = GFPORQ + FPORQ + PORQ + Q
            Semantics.table[TraceA][S_pq] = GFPORQ + FPORQ + PORQ + P + Q
            
            Semantics.table[TraceB][S_p] = GFPORQ + FPORQ + PORQ + P
            Semantics.table[TraceB][S_q] = GFPORQ + FPORQ + PORQ + Q
            Semantics.table[TraceB][S_pq] = GFPORQ + FPORQ + PORQ + P + Q
        }
    } for 5 Formula for traces_optimizer is theorem
}