# Example CNF files and S-Expression Conversion 

## Where do these examples come from?

I generated them via the [`cnfgen`](https://massimolauria.net/cnfgen/) Python library. The `cnfgen` tool can produce DIMACS standard CNF files for a variety of standard problems (including many more than I generated here as an example). 

Normally, by the time these reach DIMACS, all variables are natural numbers; the parameters for each are lost. E.g., we can know that variable `5` corresponds to (say) a certain pigeon nesting in a certain pigeonhole, but not _which ones_. Fortunately, `cnfgen` has a `--varnames` argument which we can use to embed the variable mapping into comments in the DIMACS output. 

### CNFGen Shapes

The documentation and output don't detail the exact variable mapping, so I've extracted the below from the [source code](https://github.com/MassimoLauria/cnfgen) with minor editing. In some cases, there was a comment giving the mapping, in others I had to extrapolate from code.

#### [Pigeonhole](https://github.com/MassimoLauria/cnfgen/blob/master/cnfgen/families/pigeonhole.py)

The formula is encoded with variables `p_{i,j}` for `i` in `[m]` and `j` in `[n]` where the intended meaning is that `p_{i,j}` is `True` when pigeon `i` flies into hole `j`.

#### [K-coloring of graphs](https://github.com/MassimoLauria/cnfgen/blob/master/cnfgen/families/coloring.py)

The variables are of the form `x_{v,c}` where `v` is a vertex and `c` a color. 

#### [Partitioning of elements](https://github.com/massimolauria/cnfgen/blob/master/cnfgen/families/counting.py)

The variables are of the form `x_{subset}` where `subset` is a list of element IDs. That is, if a variable is true, then the corresponding subset is part of the partition.

## Which specific examples are here?

This repo includes the original CNF files (`.cnf`) along with S-expression versions (`.scnf`) that use the provided variable mappings to produce something more semantic. The form of an `.scnf` is:

```
((p cnf <num vars> <num clauses>)
 clauses
 ...)
```
where each clause is a list of literals of the form: `(not (var <variable parameters>))` or `(var <variable parameters>)`. Parameters are extracted from the DIMACS output with `--varnames` on.

E.g., instead of a clause that looks like `(1 2 -3)`, if the `cnf` file contains a variable mapping where `1`, `2`, and `3` mean `p_{1,2}`, `p_{3,4}` and `p_{5,6}` respectively, the clause will be `((var 1 2) (var 3 4) (var 5 6))`. 

I've included the rough script used to convert (`translate.py`). 

I generated 6 CNF files:

* K-coloring of graphs:
  * `kcolor_1c_grid2x2.cnf`: a 2-by-2 grid can be 1-colored (UNSAT)
  * `kcolor_3c_grid3x3.cnf`: a 3-by-3 grid can be 3-colored (SAT)
* Pigeonhole Principle:
  * `php_3p2h.cnf`: 3 pigeons can fit into 2 pigeonholes (UNSAT)
  * `php_3p3h.cnf`: 3 pigeons can git into 3 pigeonholes (SAT)
* Partitioning elements:
  * `count_4M2p.cnf` a 4-element set can be partitioned into 2-element subsets (SAT)
  * `count_5M2p.cnf`: a 5-element set can be partitioned into 2-element subsets (UNSAT)

## Notes

I have confirmed that these 6 examples produce the expected SAT or UNSAT result using `z3 -dimacs <filename>`. 