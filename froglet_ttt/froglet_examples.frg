#lang forge/bsl

sig University {}
one sig BrownU extends University {}
sig Person {
    father: lone Person,
    mother: lone Person,
    grad: lone University
}
one sig Tim extends Person {}

pred myPred {
    -- Not OK
    -- father.grad = mother.grad
    -- OK
    some Tim.father.grad
    -- Not OK
    --some father.grad
    -- Not OK
    -- some father
    -- Not OK
    -- some father.Tim

    -- OK
    some p: Person | reachable[p, Tim, father, mother]
    -- Not OK (even though the problem is a sub-term of a builtin)
    -- some p: Person | reachable[p, father.Tim, father, mother]

}

test expect {
    myPred is sat
}