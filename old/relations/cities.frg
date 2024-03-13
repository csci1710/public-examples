#lang forge

-- Every airport has a set of other airports there are departing flights to
--   each flight having a price (there may be multiple flights from A->B with diff. prices)
sig Airport {    
    -- represented by a 3-ary relation (check the evaluator!)
    flights: set Airport -> Int    
}
-- Two airports that Brown students are likely to use
one sig PVD,BOS extends Airport {}

fun destinations[a: Airport]: set Airport {
    a.flights.Int
} 

-- What can be reached from Providence airport with at most one layover?
fun pvdAtMostOneLayover: set Airport {
  -- :-(
  --PVD.flights.Int + (PVD.flights.Int).flights.Int
  -- ...?
  -- Note because: a[b] is same as b.a
  --flights[PVD].Int + flights[flights[PVD].Int].Int  
  -- better?
  destinations[PVD] + destinations[destinations[PVD]]
}


/*
  dot and box join
  union, intersection, subtraction
  product
  "in"
  transpose, transitive closure, reflexive transitive closure

*/

/*

  A "type" is:
    a tuple of sig names, (a tuple of "sorts")
    a multiplicity (...a little imprecise?)

*/
