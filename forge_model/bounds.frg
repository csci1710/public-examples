#lang forge

/*
    Model of how numeric bounds and partial instances get translated to partial-instance bounds in Forge
    For now, the model is restricted to only _Sigs_, not also fields. We're also only concerned with explicit
    partial instances, not arbitrary formulas (as in Alcino's unpublished work).

    - omitted: `one` sigs and their effect on bounds
    - omitted: `in` subset sigs (not supported in Forge, anyway)
*/

abstract sig Modifier {}
one sig Abstract, One extends Modifier {}

sig Sig {
    modifiers: set Modifier,
    children: set Sig
}

-- TODO: 11/20/22: add "set Atom" here and the error is a *parse* error, shown in the wrong place in VSCode

sig Atom {}
-- We'd really like to write "partialUpper: pfunc Sig -> set Atom", since that would allow the function to not 
-- denote on a given sig, indicating no partial-instance bound for that sig, _distinctly from_ that bound 
-- existing and containing the empty set. But we can't write that in Forge as of November 2022. 
-- Instead, separate into two fields:
sig PartialInst {    
    atoms: set Sig -> Atom,
    isBounded: set Sig
}

sig Scope {
    -- The set of sigs with numeric bounds declared _exactly_
    exact: set Sig,
    -- The numeric scope provided (also called numeric upper bounds)
    numeric: pfunc Sig -> Int
}

fun DEFAULT_SCOPE: Int { 
    3
}

-- Assumption: all Sigs are involved in the run
one sig Run {
    scope: one Scope,

    -- The upper bounds of the given partial instance, if present
    partialUpper: one PartialInst,
    -- The lower bounds of the given partial instance, if present    
    partialLower: one PartialInst
}

pred wellformed {
    -- no cycles in the child relation
    all s: Sig | not reachable[s, s, children]

    all sc: Scope | {
        -- numeric bounds are always >= 0
        all s: Sig | some sc.numeric[s] implies sc.numeric[s] >= 0
        -- exact numeric bounds are numeric
        all s: Sig | s in sc.exact implies some sc.numeric[s]
    }

    all r: Run | {        
        -- a run either has both kinds of bounds or neither    
        some r.partialUpper iff some r.partialLower    
    }

    -- a partial instance only contains tuples for a sig if it bounds that sig (mostly for readability)
    all pi: PartialInst | pi.atoms.Atom in pi.isBounded -- ... but a bounded sig may be empty (hence in, not =)

}

---------------------------------------------------------------------------------------------------

-- Produced by algorithm
abstract sig KodkodBounds {}
lone sig ErrorBounds extends KodkodBounds {}
lone sig CompleteBounds extends KodkodBounds {
    upper: set Sig -> Atom,    
    lower: set Sig -> Atom 
}

-- Is this run "good", in that it should be able to lead to a correct kodkod bound?
pred goodRun[r: Run] {

}

test expect {
    vacuityCheckWellformed: {wellformed} is sat 
}

---------------------------------------------------------------------------------------------------
-- The bounds-resolving algorithm

-- Ideally, we'd proceed in two steps:
-- 1: Create the Alloy-style scope bounds
-- 2: Then combine them with the partial instance, if any
-- The problem with that is that the given partial instance can *name* atoms, so we need to 
-- instead begin with the partial instance, if any, and build the kodkod bounds atop it.

-- (A) Build a *total* Scope based on the numeric scopes and sig declarations.
-- (B) Starting from the _leaves_ of the sig tree, add *new atom names* to the upper/lower bounds as appropriate
--    * "one" sigs, if none already present in partial instance, add a fresh atom to both upper and lower
--    * "abstract" sigs add nothing
--    * all other sigs add the difference only to upper bounds

pred totalizedScope[partial: Scope, total: Scope] {
    -- "fake recursion" trick; relies on tree-shaped sig inheritance
    all s: Sig | {
        no s.children => {
            -- Leaf sig: either give the default, or use partial's given value
            some partial.numeric[s] => {
                total.numeric[s] = partial.numeric[s]
                s in total.exact iff s in partial.exact 
            } else {
                total.numeric[s] = DEFAULT_SCOPE
                s not in total.exact
            }
        } else {
            -- Parent sig: 
            some partial.numeric[s] => {
                total.numeric[s] = partial.numeric[s]
                s in total.exact iff s in partial.exact 
                -- caveat: need to not be exceeded by sum of children, or fail
                total.numeric[s] < (sum child : s.children | {total.numeric[child]})
            } else {
                -- sum of children
                total.numeric[s] = (sum child : s.children | {total.numeric[child]})
                s not in total.exact 
            }
        }
    }
}

pred extendScopeExampleStrict {
    wellformed 
    some s: Sig | { 
        #s.children > 1 
        all ch : s.children | Run.scope.numeric[ch] > 0
    } 
    some s: Sig | no s.children and Run.scope.numeric[s] > 0
    some r: Run, totalScope: Scope | {
        totalScope.numeric != r.scope.numeric -- diff numeric scopes
        totalizedScope[r.scope, totalScope]
    }
}

pred prop_extensionIsConsistent {
    wellformed implies {
        all totalScope : Scope | {
            totalizedScope[Run.scope, totalScope] implies {
                all s: Sig | {
                    some totalScope.numeric[s]
                    some s.children => 
                        totalScope.numeric[s] <= (sum ch: s.children | {totalScope.numeric[ch]})
                } -- end all Sig
            } -- end consequent (totalizedScope implies...)
        } -- end all Scope
    } -- end consequent (wellformed implies...)        
}

test expect {
    scopeExtensionSat: {         
        extendScopeExampleStrict         
    } is sat

    scopeExtensionConsistent: {
        prop_extensionIsConsistent
    } is theorem
    -- TODO: error message if omitting "is theorem" pretty bad -- parser error on RIGHT-CURLY-TOK
}


--run {extendScopeExampleStrict}
--run {not prop_extensionIsConsistent}

pred generateKodkod[r: Run, kb: KodkodBounds] {
    some totalScope : Scope | {
        totalizedScope[r.scope, totalScope]
        --leaves[r, kb]
    } 
    -- if no such scope exists, error
    iff not kb in ErrorBounds
}

---------------------------------------------------------------------------------------------------

-- Our correctness goals for bounds-generation
pred correctness[r: Run, kb: KodkodBounds] {
    kb in CompleteBounds => {        
        -- All sigs are implicitly bounded (kb.upper[s] empty means necessarily empty sig)
        --   (True because of how the fields are declared.)

        -- If a sig has been partially upper bounded in the run, that upper bound is respected
        all s: Sig | s in r.partialUpper.isBounded => kb.upper[s] in r.partialUpper.atoms
        -- If a sig has been partially lower bounded in the run, that lower bound is respected
        all s: Sig | s in r.partialLower.isBounded => kb.upper[s] in r.partialLower.atoms

        -- If a sig has been scoped in the run, that scope is matched in the upper-bound size
        all s: Sig | some r.numeric[s] implies r.numeric[s] = #kb.upper[s]
        -- If a sig is exact-scoped in the run, that scope is matched in the lower-bound size
        all s: Sig | s in r.scope.exact implies r.numeric[s] = #kb.lower[s]

        -- Upper bounds are supersets of lower bounds for all sigs
        all s: Sig | kb.lower[s] in kb.upper[s] 

        -- Bounds assigned are always consistent with subsorting, if applicable
        all s: Sig | all cs: s.children | {
            -- lower bound of child sig is contained in lower bound of parent sig
            kb.lower[cs] in kb.lower[s]
            -- upper bound of child sig is contained in upper bound of parent sig
            kb.upper[cs] in kb.upper[s]                        
        }
        -- child sigs are disjoint:
        --   [This is NOT something we can always guarantee by bound; sometimes we need to add additional constraints]

        -- Bounds assigned are always consisted with modifiers (one, abstract) if applicable
        all s: Sig | One in s.modifiers => {
            -- Only ever one thing 
            kb.upper[s] = kb.lower[s]
            one kb.upper[s]
        }
        all s: Sig | Abstract in s.modifiers => {
            kb.upper[s] = {}
        }


    }
}