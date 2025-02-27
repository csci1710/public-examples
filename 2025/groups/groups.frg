#lang forge 

/**
  Basic model of abstract algebra concepts. 

  Note that because I am still working on this, and I wrote it for testing out visualization,
  there are some notes-to-self in the model file. These can be ignored.

  Tim (Spring 2025)
*/

sig Element {}
/** A set with a closed, well-defined binary operation */
sig Groupoid { 
    eles: set Element,
    op: pfunc Element -> Element -> Element
}
pred groupoid[g: Groupoid] {
    // The operation is closed 
    g.op[Element][Element] in g.eles 
    // The operation is total on the groupoid
    g.op.Element = g.eles -> g.eles
}

pred group[g: Groupoid] {
    // A group is always a groupoid
    groupoid[g]
    // Identity
    some id: g.eles | {
        all e: g.eles | g.op[e, id] = e and g.op[id, e] = e
        // Associativity 
        all e1, e2, e3: g.eles | g.op[g.op[e1,e2], e3] = g.op[e1, g.op[e2,e3]]
        // Inverses
        all e: g.eles | some einv: g.eles | g.op[e, einv] = id and g.op[einv, e] = id
    }
}

pred commutative[g: Groupoid] {
    // Commutativity
    all e1, e2: g.eles | g.op[e1][e2] = g.op[e2][e1]
}

/** Show a single group (with no extraneous elements outside of it) 
 
  Already a directed graph is not really great for visualizing a binary operator. 
  Students have previously written domain-specific visualizers that produce 
  Cayley tables, etc. Projection can be used in the default visualizer, too.
  */
showAGroup: run { 
    some g: Groupoid | group[g] and Element = g.eles
} for exactly 1 Groupoid, 5 Element

/**
  Now suppose I want to model group action on a set. To keep things simple for now, 
  we'll think about a specific symmetric group: S_3, which has 6 elements. I'll
  encode this as a predicate rather than a partial instance, for reusability in assertions.
*/

pred S_3[g: Groupoid] {
    // This is a group.
    group[g]

    some disj p123, p132, p213, p231, p312, p321 : g.eles | {
        // This is an order-6 group.
        g.eles in p123 + p132 + p213 + p231 + p312 + p321

        // Now define all 36 entries. Unfortunately, this will not be abelian, 
        // so we need to fill in the full 36-element table. First, the identity:
        g.op[p123][p123] = p123
        g.op[p123][p132] = p132
        g.op[p123][p213] = p213
        g.op[p123][p231] = p231
        g.op[p123][p312] = p312
        g.op[p123][p321] = p321

        g.op[p132][p123] = p132
        g.op[p132][p132] = p123
        g.op[p132][p213] = p312
        g.op[p132][p231] = p321
        g.op[p132][p312] = p213
        g.op[p132][p321] = p231

        g.op[p213][p123] = p213
        g.op[p213][p132] = p231
        g.op[p213][p213] = p123
        g.op[p213][p231] = p132
        g.op[p213][p312] = p321
        g.op[p213][p321] = p312

        g.op[p231][p123] = p231
        g.op[p231][p132] = p213
        g.op[p231][p213] = p321
        g.op[p231][p231] = p312
        g.op[p231][p312] = p123
        g.op[p231][p321] = p132

        g.op[p312][p123] = p312
        g.op[p312][p132] = p321
        g.op[p312][p213] = p132
        g.op[p312][p231] = p123
        g.op[p312][p312] = p231
        g.op[p312][p321] = p213

        g.op[p321][p123] = p321
        g.op[p321][p132] = p312
        g.op[p321][p213] = p231
        g.op[p321][p231] = p213
        g.op[p321][p312] = p132
        g.op[p321][p321] = p123
    }
}

showS_3: run { 
    some g: Groupoid | S_3[g] and Element = g.eles
} for exactly 1 Groupoid, 6 Element

/*
  There are really 2 kinds of projection we might want: existential and universal.
  That is:
    - Alloy-style "for each value, a separate projection"
      Good for "show me the operator graph if the first operand is X" in this model
    - collapsing that dimension completely, keeping everything else
      Good for removing weights from a WDG (easier to do with a helper "view" predicate)

  I wanted CnD to allow me to say which index is source/sink. But this is just a view, 
  isn't it? Like the 2nd kind of projection. The 1st kind of projection cannot be 
  done in this way, because it induces different "sub-instances" per atom in the 
  projected sig. Collapsing gives just one.

  So is the answer: "tell CnD the name of a function..." or even "tell CnD the relations 
  you wish to visualize"? (Although, is this "hiding information"? In my case it isn't.)


*/

