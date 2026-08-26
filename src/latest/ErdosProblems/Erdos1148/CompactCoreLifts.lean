import ErdosProblems.Erdos1148.ModularCompactCore
import ErdosProblems.Erdos1148.ClosePairImage
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Uniformly bounded representatives over a fixed compact core -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_compactCore_bounded_lifts (H : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ modularCompactCore H,
      ∃ g : SL(2, ℝ), modularMk g = x ∧ ∀ i j : Fin 2, |g i j| ≤ A := by
  let K : Set SL(2, ℝ) := (fun g : SL(2, ℝ) => g • UpperHalfPlane.I) ⁻¹'
    ModularGroup.truncatedFundamentalDomain (H ^ 2)
  have hK : IsCompact K := UpperHalfPlane.isProperMap_smul_I.isCompact_preimage
    (ModularGroup.isCompact_truncatedFundamentalDomain (H ^ 2))
  let f : SL(2, ℝ) → ℝ := fun g => |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1|
  have hf : Continuous f := by
    exact (((continuous_realMatrixEntry 0 0).abs.add (continuous_realMatrixEntry 0 1).abs).add
      (continuous_realMatrixEntry 1 0).abs).add (continuous_realMatrixEntry 1 1).abs
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max A 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  rintro x ⟨g, hg, rfl⟩
  refine ⟨g, rfl, ?_⟩
  have hnorm := (hA g hg).trans (le_max_left A 1)
  have hnonneg : 0 ≤ f g := by dsimp [f]; positivity
  rw [Real.norm_of_nonneg hnonneg] at hnorm
  dsimp only [f] at hnorm
  intro i j
  fin_cases i <;> fin_cases j
  · change |g 0 0| ≤ _
    linarith [abs_nonneg (g 0 1), abs_nonneg (g 1 0), abs_nonneg (g 1 1)]
  · change |g 0 1| ≤ _
    linarith [abs_nonneg (g 0 0), abs_nonneg (g 1 0), abs_nonneg (g 1 1)]
  · change |g 1 0| ≤ _
    linarith [abs_nonneg (g 0 0), abs_nonneg (g 0 1), abs_nonneg (g 1 1)]
  · change |g 1 1| ≤ _
    linarith [abs_nonneg (g 0 0), abs_nonneg (g 0 1), abs_nonneg (g 1 0)]

theorem exists_compactCore_integral_bounded_lifts (H : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ g : SL(2, ℝ), modularMk g ∈ modularCompactCore H →
      ∃ γ : SL(2, ℤ), ∀ i j : Fin 2, |((γ : SL(2, ℝ)) * g) i j| ≤ A := by
  obtain ⟨A, hA, hlift⟩ := exists_compactCore_bounded_lifts H
  refine ⟨A, hA, ?_⟩
  intro g hg
  obtain ⟨h, hmk, hh⟩ := hlift (modularMk g) hg
  obtain ⟨γ, hγ⟩ := (modularMk_eq_iff g h).mp hmk.symm
  exact ⟨γ, by simpa only [hγ] using hh⟩

end Erdos1148.DukeArithmetic
