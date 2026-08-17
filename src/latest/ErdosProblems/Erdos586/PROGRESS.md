# Erdős 586 formalization progress

- Phase: final verification complete.
- Verified: every module under `ErdosProblems/Erdos586/` and the public
  `Erdos586.lean` theorem type-check with Lean 4.33.0 under default limits.
  The exact 10,000-prime computation in `Certificate.lean` is kernel-checked.
- Verified mathematics: `tex/586.tex` has passed an independent proof and
  constants audit; its exact certificate ends at `12644.436 < 13000`, and
  its terminal tail budget is `0.8550103984... < 1`.
- Verified formal endpoints: the sharp smooth bounds `1/3`, `31/36`, and
  `17/10`; the concrete class-mass and second-moment bridges; the finite
  certificate and analytic tail; and the final contradiction for a minimal
  divisibility antichain cover.
- Final checks: the public theorem has the exact raw list statement, the
  forbidden-shortcut search is clean, and its dependency printout contains
  only standard Mathlib logical foundations.
