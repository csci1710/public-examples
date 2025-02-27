#lang forge 

open "groups.frg" 

///////////////////////////////////////////////////////////
// Simple satisfiability checks (tests of inclusion)
///////////////////////////////////////////////////////////

// Not every groupoid is a group.
groupoid_not_group: assert {some g: Groupoid | groupoid[g] and not group[g]} is sat for 1 Groupoid

// These entail similar checks on groupoid[g], so those are omitted.
group_order_1: assert {some g: Groupoid | group[g] and #g.eles = 1} is sat for 1 Groupoid
group_order_2: assert {some g: Groupoid | group[g] and #g.eles = 2} is sat for 1 Groupoid
group_order_3: assert {some g: Groupoid | group[g] and #g.eles = 3} is sat for 1 Groupoid
group_order_4: assert {some g: Groupoid | group[g] and #g.eles = 4} is sat for 1 Groupoid

group_abelian: assert {some g: Groupoid | group[g] and commutative[g]} 
  is sat for 1 Groupoid

// The smallest non-abelian group is order 6
group_not_abelian: assert {some g: Groupoid | group[g] and not commutative[g]} 
  is sat for 1 Groupoid, 6 Element

// Test the predicate-encoded example (symmetric group of order 3)
group_s_3: assert {some g: Groupoid | S_3[g] } 
  is sat for 1 Groupoid, exactly 6 Element

///////////////////////////////////////////////////////////
// Simple tests of exclusion
///////////////////////////////////////////////////////////

// The smallest non-abelian group is order 6
group_not_abelian_small: assert {some g: Groupoid | group[g] and not commutative[g]} 
  is unsat for 1 Groupoid, 5 Element
