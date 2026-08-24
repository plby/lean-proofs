/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Set

/-!
# Erdős Problem 442

The answer is negative.
-/

namespace Erdos442

section Specification

/-- The truncated logarithm used in the upstream statement. -/
noncomputable def Real.maxLogOne (x : ℝ) : ℝ := max x.log 1

namespace Set

variable (A : Set ℕ) (x : ℝ)

/-- The finite upper-triangular set of pairs in `A ∩ [1, x]`. -/
@[inline]
abbrev bddProdUpper : Set (ℕ × ℕ) :=
  {y ∈ (A ∩ Icc 1 ⌊x⌋₊) ×ˢ (A ∩ Icc 1 ⌊x⌋₊) | y.1 < y.2}

noncomputable instance boundedIccFintype : Fintype ↥(A ∩ Icc 1 ⌊x⌋₊) :=
  ((Set.finite_Icc 1 ⌊x⌋₊).subset inter_subset_right).fintype

noncomputable instance : Fintype ↥(bddProdUpper A x) :=
  (((Set.finite_Icc 1 ⌊x⌋₊).prod (Set.finite_Icc 1 ⌊x⌋₊)).subset <| by
    rintro ⟨a, b⟩ hab
    exact ⟨hab.1.1.2, hab.1.2.2⟩).fintype

end Set

end Specification

section Counterexample

theorem not_erdos_442 : ¬ ∀ (A : Set ℕ),
    Tendsto (fun x : ℝ ↦ 1 / Real.maxLogOne (Real.maxLogOne x) *
      ∑ n ∈ (A ∩ Icc 1 ⌊x⌋₊ : Set ℕ), (1 : ℝ) / n) atTop atTop →
    Tendsto (fun x : ℝ ↦ 1 / (∑ n ∈ (A ∩ Icc 1 ⌊x⌋₊ : Set ℕ),
      (1 : ℝ) / n) ^ 2 * ∑ nm ∈ Set.bddProdUpper A x,
        (1 : ℝ) / nm.1.lcm nm.2) atTop atTop := by
  sorry
