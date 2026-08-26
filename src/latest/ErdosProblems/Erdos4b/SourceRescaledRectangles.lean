/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceSmoothRectangle
import ErdosProblems.Erdos4b.SourceTensorRescale

/-!
# Unit-simplex rectangle families give source-sized smooth profiles

The only losses in the quotient are the factor ten from shrinking the
simplex and the fixed companion energy.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem sourceIntervalIndicator_rescale (a b t : ℝ) {R : ℝ} (hR : 0 < R) :
    sourceIntervalIndicator (a / R) (b / R) t = sourceIntervalIndicator a b (R * t) := by
  have hm : t ∈ Set.Ioo (a / R) (b / R) ↔ R * t ∈ Set.Ioo a b := by
    simp only [Set.mem_Ioo, div_lt_iff₀ hR, lt_div_iff₀ hR, mul_comm t R]
  simp only [sourceIntervalIndicator, Set.indicator_apply, hm]

theorem sourceRectangleFactors_rescale {ι J : Type*}
    (a b c : J → ι → ℝ) {R : ℝ} (hR : 0 < R) :
    sourceRectangleFactors (fun j i ↦ a j i / R) (fun j i ↦ b j i / R) c =
      fun j i t ↦ sourceRectangleFactors a b c j i (R * t) := by
  funext j i t
  unfold sourceRectangleFactors
  rw [sourceIntervalIndicator_rescale _ _ _ hR]

theorem exists_sourceProfile_of_unitRectangles {K : ℕ} {J : Type*} (hK : 0 < K)
    (S : Finset J) (a b c : J → Fin K → ℝ)
    (hb : ∀ j ∈ S, ∀ i, 0 ≤ b j i)
    (hbudget : ∀ j ∈ S, (∑ i, b j i) ≤ (1 : ℝ))
    (hI : 0 < sourceTensorEnergy S (sourceRectangleFactors a b c))
    (hJ : ∀ h : Fin K, 0 < sourceTensorFaceEnergy S (sourceRectangleFactors a b c) h)
    {L : ℝ} (hL : 10 * sourceCompanionEnergy * L <
      (∑ h : Fin K, sourceTensorFaceEnergy S (sourceRectangleFactors a b c) h) /
        sourceTensorEnergy S (sourceRectangleFactors a b c)) :
    ∃ F : J → Fin K → ℝ → ℝ, SourceProfileConditions S F sourceCompanionProfile ∧
      L < sourceProfileRatio S F sourceCompanionProfile := by
  let a' := fun j i ↦ a j i / 10
  let b' := fun j i ↦ b j i / 10
  have hten : (0 : ℝ) < 10 := by norm_num
  have heq : sourceRectangleFactors a' b' c =
      fun j i t ↦ sourceRectangleFactors a b c j i (10 * t) :=
    sourceRectangleFactors_rescale a b c hten
  apply exists_sourceProfile_of_rectangles hK S a' b' c
  · intro j hj i
    exact div_nonneg (hb j hj i) (by norm_num)
  · intro j hj
    change (∑ i, b j i / 10) ≤ (1 : ℝ) / 10
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (hbudget j hj) (by norm_num)
  · rw [heq, sourceTensorEnergy_rescale S _ hten]
    exact mul_pos (inv_pos.mpr (pow_pos hten _)) hI
  · intro h
    rw [heq, sourceTensorFaceEnergy_rescale S _ hten]
    exact mul_pos (inv_pos.mpr (pow_pos hten _)) (hJ h)
  · rw [heq, sourceTensorRatio_rescale S _ hten]
    rw [lt_div_iff₀ sourceCompanionEnergy_pos, lt_div_iff₀ hten]
    nlinarith [hL]

end

end Erdos4b
