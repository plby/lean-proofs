/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.B1SquarefreeMass
import ErdosProblems.Erdos822.FilteredInputSize

/-! # Linearly many inputs from the fully filtered GIL cofactors -/

namespace Erdos822

open Filter

noncomputable def gilOuterInputs (N S : ℕ) (C : ℝ) : Finset ℕ :=
  outerInputs (fun _ ↦ gilCofactors N S C) (N ^ 60)

theorem gilOuterInputs_bounded (N S : ℕ) (C : ℝ) :
    ∀ n ∈ gilOuterInputs N S C, n ≤ N ^ 60 :=
  outerInputs_bounded _ _

theorem exists_eventually_gilOuterInputs_card_linear :
    ∃ S : ℕ, ∃ C c : ℝ, 101 ≤ S ∧ 0 < C ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        c * (N : ℝ) ^ 60 ≤ (gilOuterInputs N S C).card := by
  obtain ⟨S, C, c, hS, hC, hc, hmass⟩ := exists_eventually_sum_inv_gilCofactors_lower
  refine ⟨S, C, c / 1200, hS, hC, by positivity, ?_⟩
  simpa only [gilOuterInputs, Nat.cast_pow] using
    eventually_outerInputs_card_linear_of_log_mass hc (fun N ↦ gilCofactors_subset_oddRaw N S C) hmass

#print axioms exists_eventually_gilOuterInputs_card_linear

end Erdos822
