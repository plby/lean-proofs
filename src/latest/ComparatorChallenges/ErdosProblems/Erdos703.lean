/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos703

/-- No two members of `𝓕`, including a member paired with itself, meet in `r` points. -/
def AvoidsRIntersection (r : ℕ) (𝓕 : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, #(A ∩ B) ≠ r

open scoped Classical in
/-- The extremal quantity in Erdős Problem 703. -/
noncomputable def T (n r : ℕ) : ℕ :=
  (((range n).powerset.powerset).filter (AvoidsRIntersection r)).sup card

theorem erdos_703 :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n r : ℕ), ε * n < r → r < (1 / 2 - ε) * n →
        (T n r : ℝ) < (2 - δ) ^ n := by
  sorry

end Erdos703
