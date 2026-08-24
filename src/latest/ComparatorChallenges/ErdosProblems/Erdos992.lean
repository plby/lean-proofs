/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Set Filter MeasureTheory

namespace Erdos992

/-! ## The discrepancy in the problem -/

/-- The number of the first `N` fractional parts lying in `[a,b)`. -/
noncomputable def intervalCount (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (a b : ℝ) : ℕ :=
  ((Finset.range N).filter fun n ↦ Int.fract (α * (x n : ℝ)) ∈ Ico a b).card

/-- The type of half-open subintervals of `[0,1]`, represented by endpoints. -/
def UnitSubinterval := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}

/-- The signed error associated with one interval. -/
noncomputable def intervalError (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (I : UnitSubinterval) : ℝ :=
  intervalCount x α N I.1.1 I.1.2 - (I.1.2 - I.1.1) * N

/-- The unnormalised interval discrepancy from Erdős Problem 992. -/
noncomputable def intervalDiscrepancy (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup (Set.range fun I : UnitSubinterval ↦ |intervalError x α N I|)

theorem not_erdos_992 :
    ∃ x : ℕ → ℤ, StrictMono x ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᵐ α : ℝ ∂volume, α ∈ Icc 0 1 →
          ∃ᶠ N : ℕ in atTop,
            c * Real.sqrt ((N : ℝ) * Real.log N) ≤
              intervalDiscrepancy x α N := by
  sorry

end Erdos992
