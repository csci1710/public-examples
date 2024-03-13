/*
  Basic KD-Tree model, written by Tim in 2018-2019 upon
  taking over 0320. The question was: _why_ does the search
  in a KD-Tree need to sometimes recur into both children of
  some node? This model produces examples where it's necessary.

  This version is more complex than I remembered; it doesn't just
  model the BST-style downward search and find a scenario where 
  that doesn't suffice to find a nearest-neighbor. Instead, it uses
  taxicab distance to actually follow (or try to follow) the KD-tree 
  search in full.

  This version also badly needs some cleanup and validation. But 
  saving it as-is for now, with only minor cleanup. E.g., I changed
  a few "one"s to "some"s.
    - Comments by Tim, January 2024
*/

-- We'll use state to model the progression of the search.
open util/ordering[State]
open util/integer

abstract sig Dim {}
one sig X extends Dim{}
one sig Y extends Dim{}

sig Node {
	left: lone Node,
	right: lone Node,
	x: one Int, 
	y: one Int,
	level: one Dim
}{
    -- for readability
	x >=0 and y >=0
}

fact KDTree{
    -- There is a unique root node
	one n: Node | {all m: Node-n | m in n.^(left +right)}

	all n: Node | {
        -- no cycles
		n not in n.^(left + right)
        -- strictly alternate between X and Y dimensions
		some n.left implies n.left.level = Dim - n.level 
		some n.right implies n.right.level = Dim - n.level
        -- a left (right) child has no right (left) parents; parent is unique
        -- CLEANUP: this could be simplified
		n in Node.left implies {one {m:Node | m.left = n} and n not in Node.right}
		n in Node.right implies {one {m:Node | m.right = n} and n not in Node.left}
		
        -- the KD-tree invariant
		{n.level = X and some n.left} implies {
			all m: n.left.*(left + right) | m.x < n.x
		}
		{n.level = X and some n.right} implies {
			all m: n.right.*(left + right) | m.x >= n.x
		}
		{n.level = Y and some n.left} implies {
			all m: n.left.*(left + right) | m.y < n.y
		}

		{n.level = Y and some n.right} implies {
			all m: n.right.*(left + right) | m.y >= n.y
		}
	}
    -- node coordinates are unique
	all n: Node | no {m:Node-n | n.x = m.x and n.y = m.y}
}

run {} for exactly 5 Node, 10 State, 5 int

sig State {
	current: one Node,
	closest: lone Node,
	minDist: lone Int,
	explored: set Node
}

-- Arbitrary goal to search for (or for a nearest neighbor of)
one sig Goal {
	goal_x: one Int,
	goal_y: one Int
}{
	goal_x >= 0 and goal_y >= 0
}

-- Initial state: we've explored nothing, start at root
fact initState {
	first.current not in Node.(left + right)
	no first.closest
	no first.minDist
	no first.explored
}

fun abs[a, b: Int]: Int {
	a < b implies minus[b,a] 
	else minus[a,b]
}

-- Transition relation from old to new state
-- CLEANUP: this can almost certainly be simplified
pred recur[old, new: State]{
	some old.explored implies {
		add[abs[old.current.x, Goal.goal_x],abs[old.current.y, Goal.goal_y]] < old.minDist implies{
			new.minDist = add[abs[old.current.x, Goal.goal_x],abs[old.current.y, Goal.goal_y]]
			new.closest = old.current
		}
		else{
			new.closest = old.closest
			new.minDist = old.minDist
		}
		new.explored = old.explored + old.current

		{some old.current.left and some old.current.right} implies{
			old.current.left not in old.explored and old.current.right not in old.explored implies{
				add[abs[old.current.left.x, Goal.goal_x],abs[old.current.left.y, Goal.goal_y]] < add[abs[old.current.right.x, Goal.goal_x],abs[old.current.right.y, Goal.goal_y]] implies new.current = old.current.left
				else new.current = old.current.right
			}
			old.current.left not in old.explored and old.current.right in old.explored implies{
				new.current = old.current.left
			}
			old.current.right not in old.explored and old.current.left in old.explored implies{
				new.current = old.current.right
			}
			{old.current.(right+ left) in old.explored} implies {
				old.current in Node.(left+right) implies new.current = {m:Node | old.current in m.(left + right)}
				else new.current = old.current
			}
		}
		{some old.current.(left+right)} implies{
			old.current.(left + right) in old.explored implies {
				old.current in Node.(left+right) implies new.current = {m:Node | old.current in m.(left + right)}
				else new.current = old.current
			}
			some old.current.left and old.current.left not in old.explored implies {new.current = old.current.left}
			some old.current.right and old.current.right not in old.explored implies {new.current = old.current.right}
			
		}
		{no old.current.left or no old.current.right} implies{
			old.current in Node.(left+right) implies new.current = {m:Node | old.current in m.(left + right)}
			else new.current = old.current
		}
		
	}
	else{
		{some old.current.left and some old.current.right} implies{
			old.current.level = X implies { 
				Goal.goal_x < old.current.x implies new.current = old.current.left
				Goal.goal_x >= old.current.x implies new.current = old.current.right
			}
			old.current.level = Y implies { 
				Goal.goal_x < old.current.y implies new.current = old.current.left
				Goal.goal_x >= old.current.y implies new.current = old.current.right
			}
			new.closest = old.closest
			new.minDist = old.minDist
			new.explored = old.explored
		}
		{some old.current.left and no old.current.right} implies{
			old.current.level = X implies{ 
				Goal.goal_x < old.current.x implies {
					new.current = old.current.left
					new.minDist = old.minDist
					new.closest = old.closest
					new.explored = old.explored
				}
				Goal.goal_x >= old.current.x implies {
					new.closest = old.current
					new.minDist = add[abs[new.closest.x, Goal.goal_x],abs[new.closest.y, Goal.goal_y]]
					new.current = old.current
					new.explored = old.current
				}
			}
			old.current.level = Y implies{ 
				Goal.goal_x < old.current.y implies {
					new.current = old.current.left
					new.minDist = old.minDist
					new.closest = old.closest
					new.explored = old.explored
				}
				Goal.goal_x >= old.current.y implies {
					new.closest = old.current
					new.minDist = add[abs[new.closest.x, Goal.goal_x],abs[new.closest.y, Goal.goal_y]]
					new.current = old.current
					new.explored = old.current
				}
			}
		}
		{some old.current.right and no old.current.left} implies{
			old.current.level = X implies{ 
				Goal.goal_x < old.current.x implies {
					new.closest = old.current
					new.minDist = add[abs[new.closest.x, Goal.goal_x],abs[new.closest.y, Goal.goal_y]]
					new.current = old.current
					new.explored = old.current
				}
				Goal.goal_x >= old.current.x implies {
					new.current = old.current.right
					new.minDist = old.minDist
					new.closest = old.closest
					new.explored = old.explored
				}
			}
			old.current.level = Y implies{ 
				Goal.goal_x < old.current.y implies {
					new.closest = old.current
					new.minDist = add[abs[new.closest.x, Goal.goal_x],abs[new.closest.y, Goal.goal_y]]
					new.current = old.current
					new.explored = old.current
				}
				Goal.goal_x >= old.current.y implies {
					new.current = old.current.right
					new.minDist = old.minDist
					new.closest = old.closest
					new.explored = old.explored
				}
			}
		}
		no old.current.(left + right) implies {
			new.closest = old.current
			new.minDist = add[abs[new.closest.x, Goal.goal_x],abs[new.closest.y, Goal.goal_y]]
			new.current = old.current
			new.explored = old.current
		}
	}
	
}

-- Find a trace of the system (initial state is already a fact)
-- We'll end in the "last" state, whereever that is.
fact traces {
	all s: State-last | recur[s,s.next]
}

assert final_closest_optimal_by_taxicab_distance {
	all n: Node-last.closest | add[abs[n.x, Goal.goal_x],abs[n.y, Goal.goal_y]] >= last.minDist
}
check final_closest_optimal_by_taxicab_distance for exactly 6 Node, 13 State, 4 int

run {some first.current.left and some first.current.right} for exactly 6 Node, 13 State, 4 Int

---------------------------------------------------------------------------------------
-- CLEANUP: This old model badly needs more validation. I'm not really confident in the 
-- transition predicate now, because it's so complex I don't understand it (and even if
-- it was simpler, I'd mistrust it without validation!)

