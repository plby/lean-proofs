import ErdosProblems.Erdos1148.ClosePairLiftUniqueness
import ErdosProblems.Erdos1148.CompactCoreLifts
import ErdosProblems.Erdos1148.CompactSubsetLifts

/-! # A uniform lift-uniqueness radius over a compact modular core -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_compact_lift_radius {K : Set ModularOrbitSpace} (hK : IsCompact K) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 192 ∧
      ∀ g h : SL(2, ℝ), modularMk g ∈ K →
        EntryCloseOne (η * Real.exp 1) (g⁻¹ * h) →
        (modularMk g, modularMk h) ∈ modularClosePairs η →
        EntryCloseOne η (g⁻¹ * h) := by
  obtain ⟨A, hA, hlifts⟩ := exists_compact_integral_bounded_lifts hK
  let η := min (1 / 192 : ℝ) (1 / (32 * (A ^ 2 + 1) * Real.exp 1))
  have hden : 0 < 32 * (A ^ 2 + 1) * Real.exp 1 := by positivity
  have hηpos : 0 < η := lt_min (by norm_num) (one_div_pos.mpr hden)
  have hηsmall : η ≤ 1 / 192 := min_le_left _ _
  have hbound : η * (32 * (A ^ 2 + 1) * Real.exp 1) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hαpos : 0 < η * Real.exp 1 := mul_pos hηpos (Real.exp_pos _)
  have hbound' : 32 * (A ^ 2 + 1) * (η * Real.exp 1) ≤ 1 := by nlinarith [hbound]
  have hnonneg : 0 ≤ A ^ 2 * (η * Real.exp 1) := mul_nonneg (sq_nonneg A) hαpos.le
  have hαone : η * Real.exp 1 ≤ 1 := by nlinarith
  have hscale : 16 * A ^ 2 * (η * Real.exp 1) < 1 := by nlinarith
  have hηα : η ≤ η * Real.exp 1 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) hηpos.le
  refine ⟨η, hηpos, hηsmall, ?_⟩
  intro g h hg hclose hpair
  obtain ⟨γ, hγ⟩ := hlifts g hg
  have heq : ((γ : SL(2, ℝ)) * g)⁻¹ * ((γ : SL(2, ℝ)) * h) = g⁻¹ * h := by group
  have hclose' : EntryCloseOne (η * Real.exp 1)
      (((γ : SL(2, ℝ)) * g)⁻¹ * ((γ : SL(2, ℝ)) * h)) := by rwa [heq]
  have hpair' : (modularMk ((γ : SL(2, ℝ)) * g),
      modularMk ((γ : SL(2, ℝ)) * h)) ∈ modularClosePairs η := by
    simpa only [modularMk_integral_mul] using hpair
  have h := entryCloseOne_of_close_lifts_and_modularClosePairs hA.le hαpos.le hαone hηα
    hscale ((γ : SL(2, ℝ)) * g) ((γ : SL(2, ℝ)) * h) hγ hclose' hpair'
  rwa [heq] at h

theorem exists_compactCore_lift_radius (H : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 192 ∧
      ∀ g h : SL(2, ℝ), modularMk g ∈ modularCompactCore H →
        EntryCloseOne (η * Real.exp 1) (g⁻¹ * h) →
        (modularMk g, modularMk h) ∈ modularClosePairs η →
        EntryCloseOne η (g⁻¹ * h) :=
  exists_compact_lift_radius (isCompact_modularCompactCore H)

end Erdos1148.DukeArithmetic
