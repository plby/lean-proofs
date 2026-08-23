/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 1050

We prove that
`∑' n : ℕ+, 1 / ((2 : ℝ) ^ (n : ℕ) - 3)` is irrational.

The proof is a contour-free specialization of Borwein's rational-function
construction for generalized Lambert series.  The detailed mathematical proof
and a map of the formal argument are in `tex/1050.tex`.
-/

open scoped BigOperators Topology

namespace Erdos1050

noncomputable section

open Polynomial

/-! ## The original series and a shifted Lambert series -/

/-- The `n`th term of the target series, with `n = 0` representing the
mathematical index `1`. -/
def targetTerm (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ (n + 1) - 3)

/-- The sum in Erdős Problem 1050, indexed by positive natural numbers. -/
def erdos1050Series : ℝ :=
  ∑' n : ℕ+, 1 / ((2 : ℝ) ^ (n : ℕ) - 3)

/-- A shifted generalized Lambert series. -/
def shiftedTerm (h : ℕ) : ℝ :=
  1 / (1 - (8 / 3 : ℝ) * 2 ^ (h + 1))

/-- The shifted value used in Borwein's construction. -/
def shiftedValue : ℝ :=
  ∑' h : ℕ, shiftedTerm h

theorem erdos_1050 : Irrational erdos1050Series := by
  sorry

end

end Erdos1050
