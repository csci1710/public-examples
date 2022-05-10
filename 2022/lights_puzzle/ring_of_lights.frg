#lang forge

/*
  When using the custom vis script, remember to click "Run" after
  asking for a new trace or config! (the script doesn't re-run automatically)
*/

option problem_type temporal

------------------------
-- Puzzle infrastructure
------------------------
abstract sig Light {
  left: one Light,  -- neighbor to left
  right: one Light  -- neighbor to right
}
var sig Lit, Unlit extends Light {}

pred ring {
  -- Connected
  all x1, x2: Light | x2 in x1.^left and x2 in x1.^right
  -- Opposites
  left = ~right
}

pred solved {
  Lit = Light
}
pred init {
    -- ONE specific init state, so we can sketch how to exclude loopback 
    --   to the very beginning
    --no Lit
    --Unlit = Light
}

pred flip[switch: Light] {
  -- Flip the switch for <switch>, which also flips the neighbors
  Lit' = Lit - {x: switch+switch.left+switch.right | x in Lit}
             + {x: switch+switch.left+switch.right | x not in Lit}
}

// Look for a long solution to the puzzle
option min_tracelength 5
run {
    ring
    init    
    always {        
        -- Do nothing for a solved board. Otherwise, flip a switch
        {            
            solved -- guard
            Lit = Lit' -- action
        } or {
            not solved -- guard
            some l: Light | flip[l] -- action
        }
        
    }
    eventually solved

    -- Loopback can't be to the beginning
    --next_state { always { some Lit }}    
    --next_state { some Lit }
} 
for exactly 5 Light
