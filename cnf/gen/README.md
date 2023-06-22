# Example CNF files and S-Expression Conversion 

## Where do these examples come from?

I generated them via the [`cnfgen`](https://massimolauria.net/cnfgen/) Python library. The `cnfgen` tool can produce DIMACS standard CNF files for a variety of standard problems (including many more than I generated here as an example). 

## Which specific examples are here?

This repo includes the original CNF files (`.cnf`) along with S-expression versions (`_t.cnf`). I've included the rough script used to convert (`translate.py`). 

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