#lang forge

option problem_type temporal

sig Car {}

-- Two different ways of expressing a list of cars
-- The model's transition predicates will use the *linked* version,
--   and update the *seq* version as a ghost variable.
one sig Stoplight {
    var root: lone Car, 
    var next: pfunc Car -> Car,
    var cars: pfunc Int -> Car
}

pred init {
    no Stoplight.root
    no Stoplight.next
    no Stoplight.cars
}

pred arrival[c: Car] {
    -- guard: the car isn't already in the queue
    c not in Stoplight.root.*(Stoplight.next)
    -- action
    no Stoplight.root => {
        Stoplight.root' = c
        no Stoplight.next'
        Stoplight.cars'= 0->c        
    } else {
        Stoplight.root' = c
        Stoplight.next' = Stoplight.next + c->Stoplight.root
        -- ghost array design choice: 0 is LAST in the queue
        Stoplight.cars'[0] = c
        all idx: Int | {
            idx > 0 => Stoplight.cars'[idx] = Stoplight.cars[subtract[idx, 1]]
            idx < 0 => no Stoplight.cars'[idx]
        }        
    }
}

pred departure[c: Car] {
    -- guard: the car is at the front of the queue (furthest from root)
    c in Stoplight.root.*(Stoplight.next)
    no Stoplight.next[c]

    -- action
    c = Stoplight.root => {
        no Stoplight.root'
        no Stoplight.next'
        no Stoplight.cars'
    } else {
        -- remove the *last* thing in the queue; no need to change root        
        Stoplight.next' = Stoplight.next - (Car->c)
        Stoplight.root' = Stoplight.root
        -- ghost array design choice: 0 is LAST in queue, we want to remove FIRST
        no Stoplight.cars'[max[inds[Stoplight.cars]]]
        all idx: Int - max[inds[Stoplight.cars]] | {
            idx >= 0 => Stoplight.cars'[idx] = Stoplight.cars[idx]
            else        no Stoplight.cars'[idx]
        }        
    }
}


pred move {
    some c: Car | arrival[c] or departure[c]
}

// NOTE for next year: Annoying that we can't set Time bound per run...

----------------------------------------------------------

pred wellformed {
    isSeqOf[Stoplight.cars, Car]  
    not hasDups[Stoplight.cars]
    
    -- not strong enough: doesn't preserve ordering
    elems[Stoplight.cars] = Stoplight.root.*(Stoplight.next)
    -- also need (the way it's written depends on the above):
    all c: Car | {
        -- Same start
        (Stoplight.cars[0] = c) iff (Stoplight.root = c)
        -- Same next
        --    Beware: add[1, none] = 1.
        let idx = idxOf[Stoplight.cars, c] | 
            c in elems[Stoplight.cars] => Stoplight.cars[add[1, idx]] = Stoplight.next[c]       
    }
}

test expect {
    wfAllowsMultiple: {
        wellformed
        #Stoplight.cars > 1
    } is sat
    
    wfPreserved: {
        always {
            (wellformed and move) implies next_state wellformed
        }
    } is theorem 
    wfInvariant: {(init and always move) implies always wellformed} is theorem

    exerciseArrivalRootNotInitial: {
        not init and wellformed -- some consistent state, but not an initial one
        no Stoplight.root
        some c: Car | arrival[c]        
    } is sat
    exerciseArrivalNotRootNotInitial: {
        not init and wellformed -- some consistent state, but not an initial one
        some Stoplight.root
        some c: Car | arrival[c]
    } is sat
    exerciseDepartureFromWellformedOne: {
        wellformed 
        one Stoplight.cars
        some c: Car | departure[c]
    } is sat
    exerciseDepartureFromWellformedMultiple: {
        wellformed 
        #Stoplight.cars > 1
        some c: Car | departure[c]
    } is sat

}

run {
    init
    always move
    eventually #Stoplight.cars > 1
} for exactly 5 Car