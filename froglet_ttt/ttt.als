open util/ordering[Board]

abstract sig Player {}
one sig X, O extends Player {} 

abstract sig Index {}
one sig A extends Index {}
one sig B extends Index {}
one sig C extends Index {}

sig Board {
    places: set Index -> Index -> Player
}

pred xturn[brd: Board] {
  #brd.places.X = #brd.places.O  
} 
pred oturn[b: Board] {
  sub[#b.places.X,1] = #b.places.O
}

pred winH[b: Board, p: Player] {
  some r: Index | all c: Index |
    p in b.places[r][c]
}

pred winV[b: Board, p: Player] {
  some c: Index | all r: Index |
    p in b.places[r][c]
}

pred winD[b: Board, p: Player] {
  A->A + B->B + C->C in b.places.p 
  or
  A->C + B->B + C->A in b.places.p 
}

pred valid[b: Board] {
  oturn[b] or xturn[b]
}
       
pred winning[b: Board, p: Player] {
  winH[b, p] or winV[b, p] or winD[b, p]
}

--------------------

pred move[pre: Board, post: Board, p: Player, r: Index, c: Index] {
    -- GUARD: no move there yet, correct turn
    no pre.places[r][c]
    p = X implies xturn[pre]
    p = O implies oturn[pre]
	-- TRANSITION: augment post-board
	post.places = pre.places + (r->c->p) 
}

pred trace {
	-- start with empty board
	no first.places
    -- always move forward (except in last state)
    all b: Board - last | 
        some p: Player, r, c: Index | 
            move[b, b.next, p, r, c]
}

--------------------

-- Check that traces always contain only wellformed boards
pred wellformed {
  all b: Board | all r: Index | all c: Index | {
    lone r.(c.(b.places)) -- <=1 entry per location
  }
}
check {
    trace implies wellformed
} for 9 Board, 3 Index, 2 Player

--------------------

-- Find me an example of a winning game for X
run {
    trace
	-- end in a winning board for X
    winning[last, X]
} for 9 Board, 3 Index, 2 Player

--------------------

-- Is it true that if I move in the middle to start, I'll win?
--  (If this succeeds, I get a counterexample.)
run {
    trace
    first.next.places = (B -> B -> X)
    no b: Board | winning[b, X]
} for 9 Board, 3 Index, 2 Player


