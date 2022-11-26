#lang forge/bsl
-- Forge roughly approximates Alloy...
-- ...and Froglet (forge/bsl) is a language level for Forge

abstract sig Player {}
one sig X, O extends Player {} 

abstract sig Index {}
one sig A extends Index {}
one sig B extends Index {}
one sig C extends Index {}

sig Board {
    -- partial function: Guarantees the wellformedness as a type constraint
    places: pfunc Index -> Index -> Player
}

pred xturn[brd: Board] {
  #brd.places.X = #brd.places.O  
} 
pred oturn[b: Board] {
  subtract[#b.places.X,1] = #b.places.O
}

pred winH[b: Board, p: Player] {
  some r: Index | all c: Index |
    b.places[r][c] = p
}

pred winV[b: Board, p: Player] {
  some c: Index | all r: Index |
    b.places[r][c] = p
}

pred winD[b: Board, p: Player] {
    (b.places[A][A] = p and 
     b.places[B][B] = p and
     b.places[C][C] = p)
    or
    (b.places[A][C] = p and 
     b.places[B][B] = p and
     b.places[C][A] = p)
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
	post.places[r][c] = p
    -- _explicit_ frame condition
    all r2, c2: Index | (r2=r and c2=c) or post.places[r2][c2] = pre.places[r2][c2]
}

one sig Trace {
    first: one Board,
    next: pfunc Board -> Board
}
pred trace {
	-- start with empty board
	all r, c: Index | no Trace.first.places[r][c]
    -- Potential error (easy to make when translating from Alloy)
    --all r, c: Index | no first.places[r][c]
    -- always move forward (except in last state)
    all b: Board | some Trace.next[b] implies {
        some p: Player, r, c: Index | 
            move[b, Trace.next[b], p, r, c]
    }
}

--------------------

run {
    trace
	-- end in a winning board for X
    some winningb: Board | no Trace.next[winningb] and winning[winningb, X]
} for 9 Board, 3 Index, 2 Player for {next is linear}


