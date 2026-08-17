/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# Erdős Problem 703: forbidden intersections

For `n r : ℕ`, `T n r` is the largest size of a family of subsets of
`{0, ..., n - 1}` such that no two members (including a member paired with
itself) have intersection of size `r`.

The main theorem `erdos_703` is the Frankl--Rödl exponential gap: if `r` stays
a positive linear distance from both `0` and `n / 2`, then `T n r` is bounded
by `(2 - δ) ^ n`, where `δ > 0` depends only on that distance.

The mathematical proof and the formalization map are in `tex/703.tex`.
-/

namespace Erdos703

open Nat Finset Real
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Two finite sets have an `r`-intersection when their intersection has size `r`. -/
def HasRIntersection (r : ℕ) (A B : Finset ℕ) : Prop :=
  #(A ∩ B) = r

/-- No two members of `𝓕`, including a member paired with itself, meet in `r` points. -/
def AvoidsRIntersection (r : ℕ) (𝓕 : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, #(A ∩ B) ≠ r

/-- The extremal quantity in Erdős Problem 703. -/
def T (n r : ℕ) : ℕ :=
  (((range n).powerset.powerset).filter (AvoidsRIntersection r)).sup card


theorem erdos_703 :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n r : ℕ), ε * n < r → r < (1 / 2 - ε) * n →
        (T n r : ℝ) < (2 - δ) ^ n := by
  sorry

end

end Erdos703
