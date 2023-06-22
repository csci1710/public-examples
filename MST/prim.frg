#lang forge

/*
Prim's algorithm in Forge
  Tim 2020, revised Nov 2021
  Made public December 2022
  Comments added to demo relational vs. Froglet in January 2023
*/

-- In 2020, this needed to be MiniSat or MiniSatProver or the solver
--   ran out of memory. But that was the full "comparison" model.
--option solver MiniSatProver -- SAT4J
option verbose 2

-------------------------------------------------------------
-- Always have a specific weighted directed graph in the background
-------------------------------------------------------------

sig Node {
    edges: set Node -> Int
}

pred wellformedgraph {
    -- no double-edges
    all n, m: Node | lone edges[n][m] 
    
    -- no negative weights
    all n, m: Node | some edges[n][m] implies edges[n][m] >= 0 
    
    -- symmetric
    -- all n, m: Node | n.edges[m] = m.edges[n] 
    edges.Int = ~(edges.Int)

    -- no self-loops
    no (iden & edges.Int)
}

pred symmetric_1 { 
    edges.Int = ~(edges.Int)
}
pred symmetric_2 {
    all n, m: Node | n.edges[m] = m.edges[n] 
}

test expect {
    {wellformedgraph implies {symmetric_1 iff symmetric_2}} is theorem
}

pred difflengthedges {
    -- Find a graph where all the edges are different lengths
    all disj n1, n2: Node | all disj m1, m2: Node | { 
        -- some n1.edges[m1] implies ...
        n1->m1 in edges.Int implies n1.edges[m1] != n2.edges[m2]                                                                                      
    }
}

-------------------------------------------------------------
-- Prim's algorithm
-------------------------------------------------------------

-- State sig for Prim's algorithm
sig Prim {
    pnodes: set Node,
    ptree: set Node->Node
}

pred prim_init[s: Prim] {
    -- Initialize to an arbitrary node; no edges in tree yet
    --some n: Node | s.pnodes = n 
    one s.pnodes -- alternative
    no s.ptree
}

pred extendPrim[pre, post: Prim] {
    -- Find the set of as-yet-unreached nodes 
    -- candidatesWithWeights : Node -> Int <-- would like to make this explicit
    let candidatesWithWeights = ((Node-pre.pnodes) -> Int) & pre.pnodes.edges |
    -- Find the cheapest cost among all candidates
    let minWeight = min[candidatesWithWeights[Node]] |
    -- Find the candidates who share that cheapest cost
    let minWeightCandidates = candidatesWithWeights.minWeight |
        some m, n: Node | { 
            m in pre.pnodes
            n in minWeightCandidates
            m->n->minWeight in edges -- probably a more efficient way to do this    
            post.pnodes = pre.pnodes + n -- prevents >1 node added at a time ("some" is safe)
            post.ptree = pre.ptree + (m -> n) + (n -> m)
        }
}

pred pnoneleft[s: Prim] {
  -- This is "cheating"; assumes valid Prim (building *one* tree)
  --s.pnodes = Node
  -- More correct (note we ASSUME symmetry in the tree):
  all disj n1, n2: Node | n1 in n2.^(s.ptree)
}


-----------------------------------------------
-- Run!
-----------------------------------------------

one sig PrimTrace {
    pnext: set Prim -> Prim
}

pred primTrace {
    -- modulo linear-ordering enforced at bounds level
    all p: Prim | some p.(PrimTrace.pnext) => extendPrim[p, p.(PrimTrace.pnext)]
    some initial: Prim | prim_init[initial]
    -- ^ TODO, isn't this something we could break the symmetry on?
}

pred runPrimComplete {
    wellformedgraph
    primTrace
    some p: Prim | pnoneleft[p] -- complete
}
run runPrimComplete for 5 Node, 5 Prim, 5 Int for {pnext is linear}

-------------------------------------------------------------
-- Validation
-------------------------------------------------------------

inst wikipedia {
  Node in `A + `B + `C + `D
  Node ni `A + `B
  edges = `A->`B->2 + `A->`D->1 + `B->`D->2 + `C->`D->3
}

--test 
expect {    
    {wellformedgraph difflengthedges} for 5 Node, 1 Prim, 5 Int is sat
}