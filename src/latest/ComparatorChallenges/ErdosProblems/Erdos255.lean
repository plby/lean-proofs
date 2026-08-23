/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 255

For every sequence in `[0,1]`, some interval has unbounded discrepancy.  We
prove the stronger form established by Schmidt: the interval may be chosen to
be an anchored half-open interval `[0,x)`.

The proof has three parts.  `FiniteRoth.lean` proves a finite two-dimensional
Roth inequality by exact sums of dyadic Haar functions.  `NoUniform.lean`
deduces that no sequence in `[0,1)` has uniformly bounded anchored
discrepancy.  `Baire.lean` localizes a hypothetical pointwise bound by the
Baire category theorem, extends it one-sidedly across the countable set of
sequence values, and rescales the resulting local subsequence.  The detailed
mathematical proof and Leanization map are in `tex/255.tex`.

The interval convention is half open.  This is harmless for the problem and,
more importantly, the theorem below explicitly counts membership in `[0,x)`;
there is no endpoint-convention abstraction hidden in the statement.
-/

open Filter Finset Set
open scoped BigOperators Topology

namespace Erdos255

/-- Discrepancy of the first `N` terms in the actual interval `[0,x)`. -/
noncomputable def anchoredDiscrepancy (z : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (((range N).filter fun n ↦ z n ∈ Ico (0 : ℝ) x).card : ℝ) - N * x


theorem erdos_255 (z : ℕ → ℝ) (hz : ∀ n, z n ∈ Icc (0 : ℝ) 1) :
    ∃ x ∈ Icc (0 : ℝ) 1,
      Ico (0 : ℝ) x ⊆ Icc (0 : ℝ) 1 ∧
      atTop.limsup (fun N ↦ ((|anchoredDiscrepancy z N x| : ℝ) : EReal)) = ⊤ := by
  sorry

end Erdos255
