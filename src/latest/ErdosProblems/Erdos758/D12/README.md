# D12 finite certificate suite

This directory records the finite twelve-vertex step in the resolution of
Erdos Problem 758:

> Every graph on twelve vertices either has a clique or independent set on
> four vertices, or its vertices partition into four homogeneous triples.

Together with the elementary eight-vertex decomposition, this gives four
cochromatic classes for every graph on twelve vertices.

## Base formula

Variables use lexicographic order:

* 1--66 are the edges `{i,j}` of `Fin 12`;
* 67--286 are indicators `h_{i,j,k}` for the 220 triples.

`base.clauses` contains 16,830 clauses without a DIMACS header:

* 990 clauses, two per four-set, exclude a clique and an independent set;
* 440 clauses force `h_t` when all three edges of `t` agree;
* 15,400 clauses, one per canonical partition into four triples, exclude
  four simultaneously true indicators.

Only the forward implication from triple homogeneity to `h_t` is required.
Consequently any model would encode a graph having neither conclusion of the
finite statement.

## Normalization and cases

Complement and relabel so vertex 0 has degree `d` in `6,...,11` and
neighborhood `{1,...,d}`.  Write `A={1,...,d}`.  The absence of a homogeneous
four-set makes `G[A]` triangle-free.  Mantel's bound therefore supplies a
vertex 1 of internal degree at most 3 for `d=6,7`, and at most 4 for `d=8`.

For `d=6,7`, relabel inside `A` so the `r` internal neighbors of vertex 1
come first.  Where present, `s` records the number of outside neighbors of
vertex 1, also moved to the front of that cell.  The 44 root cases are:

* `d=6`: `r=0,...,3` and `s=0,...,5`;
* `d=7`: the unsplit case `r=0`, and `r=1,...,3`, `s=0,...,4`;
* one initial case for each of `d=8,9,10,11`.

Ten difficult `d=6,7` roots are split by
`t=deg_B(2)`, where `B=A\(N_A(1) union {1})`.  The `d=8` root is split by
`r=0,...,4`, and its `r=1,2` cases are additionally split by `t`.  Residual
cell permutations put each newly fixed neighbor set first while preserving
the earlier rows.  This gives exactly 91 covering cases.  `manifest.json`
lists every fixed edge value in DIMACS numbering.

## Files and reconstruction

The base clause body is shared.  Each `cases/NAME.units` contains only the
normalization units for one case, while `cases/NAME.lrat` is its original
dependency-trimmed RUP proof.  These files preserve the complete reference
formula and proof.

The final Lean-facing files are in `reduced/`.  A trimmed proof refers to only
a subset of its initial clauses.  For each case, `reduce_suite.py` extracts
that subset, sorts it by original clause ID, and rewrites its proof references
to the compact CNF numbering.  Thus:

* `reduced/NAME.cnf` is the compact formula;
* `reduced/NAME.lrat` is the remapped proof;
* position `i` of `reduced/NAME.ids` gives the original one-based clause ID of
  compact clause `i+1`.

The original ID ranges are 1--990 for homogeneous four-set alternatives,
991--1430 for triple-indicator implications, 1431--16830 for four-triple
partitions, and 16831 onward for the case units.  This mapping lets the shared
semantic elaborator interpret every compact proposition without duplicating
case-specific reconstruction code.

Each independent `Cases/NAME.lean` module imports `Semantic.lean`, declares
its compact raw proof and normalization-unit list, includes the ID text, and
builds its semantic implication through a balanced range tree.  Every leaf
interprets at most 512 retained clauses; each leaf and internal merge is a
separate private theorem, and the public theorem applies the tree root to the
compact raw proof.  `Certificates.lean` is a lightweight import index for
those 91 modules.  Compiling cases separately bounds elaboration memory and
permits per-case build caching.

Regenerate the shared clause body, unit files, and Lean declaration index:

```bash
python3 generate_d12.py --write-shared --lean-index
```

Regenerate the compact suite in a separate directory and verify every
remapped RUP step independently:

```bash
python3 reduce_suite.py --output /tmp/d12-reduced
python3 verify_reduced.py /tmp/d12-reduced
```

Reconstruct a complete DIMACS input for one case:

```bash
python3 generate_d12.py --cnf d6_r2_s2_t1 --output /tmp/d12.cnf
```

The traces were generated with CaDiCaL 2.1.2, git revision
`3ff42f04384489916f017acd6d5e7cbfa7257be7`:

```bash
cadical /tmp/d12.cnf /tmp/d12.raw.lrat \
  --lrat --binary=false --quiet --plain --seed=20
python3 trim_rup_lrat.py /tmp/d12.raw.lrat /tmp/d12.lrat INITIAL_CLAUSES
```

The plain solver configuration yields RUP additions.  The trimming script
keeps the transitive dependency cone of the final empty clause.  Verify every
stored hash, proof reference, positive hint, and final contradiction with:

```bash
python3 verify_suite.py
sha256sum -c SHA256SUMS
```

## Recorded checks

There are 91 proofs totaling 71,178,169 bytes; the largest is 2,891,061
bytes.  The largest proof was reconstructed by Mathlib's `FromLRAT` at the
ordinary Lean limits in 175.394 seconds, with peak resident memory 15,607,780
KiB on the recording host.  Its foundation dependency report contained only
`propext`, `Classical.choice`, and `Quot.sound`.

The compact suite contains 2,705,457 CNF bytes and 68,604,453 proof bytes.
The largest compact formula retains 3,610 initial clauses and the largest
compact proof is 2,791,259 bytes.  The independent checker replayed 453,152
RUP additions using 9,054,887 hints and verified the exact source mapping for
all 91 cases.  The 3,610-clause semantic worst case uses eight balanced leaves
of 451 or 452 clauses.  It and the largest compact-proof module were accepted
at the ordinary Lean limits.
