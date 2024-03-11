#lang forge/temporal
option max_tracelength 10

/*
Prim's algorithm in Forge
  Tim, 2021; revised to use Temporal Forge in 2024

  For visualization, use Table View and open the "Time" side drawer to step
  through the trace; you should see a new Node being added to Prim.pnodes every step.
  
*/

-------------------------------------------------------------
-- Always have a specific weighted directed graph in the background
-------------------------------------------------------------

sig Node {
    edges: set Node -> Int
}

pred wellformedgraph {
    -- no differently-valued edges between the same nodes
    all n, m: Node | lone edges[n][m] 
    
    -- no negative weights
    all n, m: Node | some edges[n][m] implies edges[n][m] >= 0 
    
    -- symmetric
    edges.Int = ~(edges.Int)

    -- no self-loops
    no (iden & edges.Int)

    -- connected (or else it cannot be spanned)
    all disj n, m: Node | n in m.^(edges.Int)
}

-------------------------------------------------------------
-- Prim's algorithm
-------------------------------------------------------------

one sig Prim {
    var pnodes: set Node,
    var ptree: set Node->Node
}

pred prim_init {
    one Prim.pnodes -- one arbitrary node picked to start
    no Prim.ptree   -- no spanning tree edges yet
}

-- Intermediate steps represented as helper predicates

-- The set of possible nodes to expand the tree to next, along with costs
fun candidatesWithWeights: set Node -> Int { 
    ((Node-Prim.pnodes) -> Int) & Prim.pnodes.edges
}
-- The cheapest cost among all candidates
fun minCandidateWeight: set Int { 
    min[candidatesWithWeights[Node]]
}
-- The candidates who share that cheapest cost
-- (Note how you can use a helper function as a relation to join on!)
fun minWeightCandidates: set Node {
  candidatesWithWeights.minCandidateWeight 
}

-- A little code duplication here, but it enables a richer validation below
pred prim_step_enabled[m, n: Node] {
    m in Prim.pnodes             -- source node is in the set
    n in minWeightCandidates     -- destination node is a minimal hop away
    -- perhaps there's a more efficient way to do this line?
    m->n->minCandidateWeight in edges  -- there's an actual edge at this weight
}
pred prim_step[m, n: Node] {
    -- GUARD
    prim_step_enabled[m, n]
    -- ACTION/FRAME for pnodes
    Prim.pnodes' = Prim.pnodes + n 
    -- ACTION/FRAME for ptree (remember to add both symmetric edges!)
    Prim.ptree' = Prim.ptree + (m -> n) + (n -> m)
}

pred prim_doNothing {
    -- GUARD
    -- we cannot make progress using a Prim step -- DO NOT CONFUSE this with prim_step
    all m, n: Node | not prim_step_enabled[m, n]
    -- ACTION
    Prim.pnodes' = Prim.pnodes
    Prim.ptree' = Prim.ptree
}


-----------------------------------------------
-- Run!
-----------------------------------------------

pred prim_trace {
    wellformedgraph  -- require a well-formed graph
    prim_init        -- start in an initial state
    
    -- always step forward using these transitions
    always { 
        some m, n: Node | { prim_step[m, n] }
        or 
        prim_doNothing 
    }
}

-------------------------------------------------------------
-- View a run!
-------------------------------------------------------------

run prim_trace for exactly 5 Node, 5 Int

-------------------------------------------------------------
-- Model Validation
-------------------------------------------------------------

-- "Optional" predicates focusing on wellformedgraph, since our criterion for 
-- finishing Prim's is that all the nodes are in the spanning tree. We want to
-- check that certain shapes are possible *AND* that Prim's can run on those shapes.
-- (Doing both at once, since prim_trace includes wellformedgraph)

-- Find a graph where all the edges are different lengths
pred difflengthedges {
    all disj n1, n2: Node | all disj m1, m2: Node | { 
        n1->m1 in edges.Int implies n1.edges[m1] != n2.edges[m2]                                                                                      
    }
}

-- Find a graph where all possible edges are present (at some weight)
pred complete_graph {
    all disj n1, n2: Node | {
        n1->n2 in edges.Int
    }
}

-- Run most of these on arbitrary 5-node graphs to force Forge to try more realistic cases.
test expect {    
    -- Make sure we can generate and run Prim's on graphs with different/same weights
    prims_difflengths_5: {prim_trace and difflengthedges} 
      for exactly 5 Node, 5 Int is sat
    prims_samelengths_5: {prim_trace and not difflengthedges} 
      for exactly 5 Node, 5 Int is sat

    -- Make sure we can generate and run Prim's on graphs of 1 and 2 nodes 
    -- (*Don't* expect 0-node graphs to work.)
    prims_single_node: {prim_trace} 
      for exactly 1 Node, 5 Int is sat  
    prims_double_node: {prim_trace} 
      for exactly 2 Node, 5 Int is sat  

    -- Make sure we can generate and run Prim's on complete/incomplete graphs
    prims_complete_graph_5: {prim_trace and complete_graph}
      for exactly 5 Node, 5 Int is sat
    prims_non_complete_graph_5: {prim_trace and not complete_graph}
      for exactly 5 Node, 5 Int is sat
}

-- These are great, but...
-- We'd really love to check that Prim's can actually run on _every_ possible 
-- non-empty graph. The problem is that Temporal Forge only finds lasso traces,
-- so "can actually run" must fit into a lasso trace. This is why doNothing's 
-- guard is just "prim_step isn't enabled"; we want to allow even buggy lasso traces! 

test expect {
  doNothing_not_used_buggily: {
    -- Can we find a Prim trace where doNothing is used before the full tree is explored?
    prim_trace
    eventually {prim_doNothing and Prim.pnodes != Node}
  } for 5 Node, 5 Int 
  -- Hopefully not!
  is unsat
}



-------------------------------------------------------------
-- Requirements
-------------------------------------------------------------

-- (1) The spanning tree generated actually spans the graph
pred current_is_spanning {
  all disj n1, n2: Node | n1 in n2.^(Prim.ptree)
}
-- (2) The spanning tree generated is a tree
pred current_is_tree {
  -- This is subtle to express for _undirected_ trees, since Forge represents them 
  -- as symmetric directed trees. We'll say "whenever two nodes are directly 
  -- connected, removing that connection removes connectivity between them"
  all disj n1, n2: Node | n2 in n1.(Prim.ptree) implies {
    n2 not in n1.^(Prim.ptree - (n1->n2 + n2->n1))
  }
}
-- Note: make sure not to separate these into different time indexes:
--  "eventually current_is_spanning and eventually current_is_tree"
--  would allow starting as a tree but ending as a DAG!
pred req_eventually_is_spanning_tree {
    eventually {current_is_spanning and current_is_tree }
}
assert prim_trace is sufficient for req_eventually_is_spanning_tree
  for 5 Node, 5 Int

-- (3) the spanning tree generated is minimal 

-- Minimality is much harder to express for the moment. The original model
-- this was taken from ran Kruskal's algorithm too, and compared the total
-- weight of the results; this is a variation on PBT!
