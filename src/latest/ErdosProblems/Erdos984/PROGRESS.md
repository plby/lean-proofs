# Erdős 984 formalization log

- Phase 1 — complete: `tex/984.tex` gives the detailed mathematical proof,
  including the explicit finite torus/Fourier construction, sparse-scale
  interpolation, geometric-block assembly, source audit, and an exact map to
  the Lean modules.
- Phase 2 — complete: the Hunter construction is formalized without an
  assumed finite theorem.  The verified chain constructs a typical rotation,
  a localized cosine-power kernel, a positive-measure hitting set, simultaneous
  separated center groups, radial labels, the subpower finite-coloring family,
  and finally the alternating global coloring.
- Main result: `Erdos984.erdos_984 : Erdos984Statement` kernel-checks under
  Lean/Mathlib v4.33.0.
- Axiom audit: `#print axioms Erdos984.erdos_984` reports exactly
  `[propext, Classical.choice, Quot.sound]`; there is no project-local axiom.
- Passed from `src/latest/`:
  `LD_PRELOAD=/tmp/lean-proc-self.so LEAN_SYSROOT=/root/code/lean-4.33.0
  /root/code/lean-4.33.0/bin/lake build ErdosProblems.Erdos984` and the same
  environment with `lake env lean ErdosProblems/Erdos984.lean`.  The
  auxiliary non-imported rate module also passes
  `lake build ErdosProblems.Erdos984.HunterRate`.
- Forbidden-construct audit: the final `rg` scan over the main file and all
  Problem 984 modules found no forbidden proof placeholder, forbidden
  declaration form, or computational-limit override.
- Incidental failure: no TeX engine (`pdflatex`, `latex`, `xelatex`,
  `lualatex`, or `tectonic`) is installed, so the mathematical writeup was
  source-checked but not rendered.  This does not affect Lean validation.
- Next step: none; both requested phases and all Lean validations are complete.
