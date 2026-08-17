# Erdős 543 formalization progress

- Phase 1 — complete: `tex/543.tex` reconstructs the Ma–Tang proof, its
  uniform error estimates, and the Leanization map.
- Phase 2 — complete: the exact subset model, threshold monotonicity,
  prime sequence, finite probability, Bonferroni, second-moment, matrix-fiber,
  rank-stability, hypercube, low-rank counting, incidence-stratification,
  asymptotic, and independent-to-uniform transfer layers have been checked by
  Lean.
- Final integration: `CoreObstruction.eventualPrimeCyclicFailure` proves the
  prime-cyclic obstruction, and `Erdos543.erdos_543` applies it to the exact
  universal threshold.
- Verified failures resolved: direct Lean needed the repository's configured
  `LD_PRELOAD`/`LEAN_SYSROOT` wrapper; the rectangular rank-stability gap was
  closed by extracting a nonsingular maximal minor.
- Verified: the main Lean file type-checks, and `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Release audit complete: the full target and all helper modules build; the
  forbidden-token and trailing-whitespace scans return no matches.
