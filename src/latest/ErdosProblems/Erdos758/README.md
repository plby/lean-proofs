# Finite certificate for the 8-vertex reduction

`D8.cnf` is the finite SAT instance used for the `z(8) ≤ 3` reduction.
It has 84 variables and 532 clauses.

* Variables 1--28 are the edges `{i,j}` of `Fin 8`, in lexicographic
  `itertools.combinations(range(8), 2)` order.
* Variables 29--84 are indicators `h_{i,j,k}`, in lexicographic triple order.
  A satisfying assignment is forced to set `h_t` when the three edges of `t`
  have the same value; it may also set additional indicators.
* The first 140 clauses say that no four-set is a clique or an independent set.
* The next 112 clauses say `t homogeneous -> h_t` (two clauses per triple).
* The final 280 clauses say that no two vertex-disjoint triples both have their
  indicators set.  The two remaining vertices automatically form a third
  homogeneous class.

Thus a model would be a graph with neither a homogeneous four-set nor two
disjoint homogeneous triples.  `D8.lrat` refutes this instance.  It is a text
LRAT certificate containing only RUP additions; deletion lines were removed by
retaining the transitive dependency cone of the final empty clause.

The files were generated with CaDiCaL 2.1.2:

```bash
python3 generate_d8.py
cadical D8.cnf D8.raw.lrat \
  --lrat --binary=false --quiet --plain --seed=20
python3 trim_rup_lrat.py D8.raw.lrat D8.lrat 532
```

The `--plain` configuration is important: Mathlib's
`Mathlib.Tactic.Sat.FromLRAT` elaborator accepts RUP proofs, not general RAT
steps.  A syntactic audit checks that every post-clause hint is positive.

Expected SHA-256 digests:

```text
5cd6ce39c3e0cb6a1b748ef5f436164f9ec9a01f78499d046ed7973868fa5420  D8.cnf
8e8801f00bf259ceab5678cc3e93c17a7a31db38a0d3bb1c0fe516b87f638b7e  D8.lrat
```

