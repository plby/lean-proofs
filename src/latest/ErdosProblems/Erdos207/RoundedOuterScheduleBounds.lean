/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RoundedOuterQuadraticBarrier

/-!
# Uniform consequences of a rounded outer corridor

This module converts the time-varying quadratic corridor into the few
uniform floor, ceiling, and availability bounds consumed by the initial
product-law theorem.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

lemma roundedQuadraticUpper_antitone_on
    {N coefficient R0 slope : ℝ≥0} {buffer : ℝ} {fuel i j : ℕ}
    (hpos : (fuel : ℝ≥0) * slope < R0) (hij : i ≤ j) (hj : j ≤ fuel) :
    roundedQuadraticUpper N coefficient R0 slope buffer j ≤
      roundedQuadraticUpper N coefficient R0 slope buffer i := by
  unfold roundedQuadraticUpper nonnegativeNatCeil
  apply Nat.ceil_mono
  apply max_le_max_left
  simpa only [add_comm] using add_le_add_right
    (quadraticPairBarrier_antitone_on hpos hij hj) buffer

lemma roundedQuadraticLower_antitone_on
    {N coefficient R0 slope : ℝ≥0} {buffer : ℝ} {fuel i j : ℕ}
    (hpos : (fuel : ℝ≥0) * slope < R0) (hij : i ≤ j) (hj : j ≤ fuel) :
    roundedQuadraticLower N coefficient R0 slope buffer j ≤
      roundedQuadraticLower N coefficient R0 slope buffer i := by
  unfold roundedQuadraticLower nonnegativeNatFloor
  apply Nat.floor_mono
  apply max_le_max_left
  exact sub_le_sub_right
    (quadraticPairBarrier_antitone_on hpos hij hj) buffer

/-- A rounded corridor and its two endpoint bounds imply the exact uniform
certificate required by `outerSharpRecursive_absorberInitialProductLaw`. -/
theorem outerSharpUniformBounds_of_roundedCorridor
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ : ℕ) (buffer : ℝ) (Kinc fuel : ℕ)
    (N upperCoefficient lowerCoefficient upperR0 lowerR0
      upperSlope lowerSlope : ℝ≥0)
    (dmin Umax reserve Dcut : ℕ)
    (hupperPos : (fuel : ℝ≥0) * upperSlope < upperR0)
    (hlowerPos : (fuel : ℝ≥0) * lowerSlope < lowerR0)
    (hschedules : ∀ i, i ≤ fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        roundedQuadraticUpper N upperCoefficient upperR0 upperSlope buffer i ∧
      roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope buffer i ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ∧
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
    (hdmin : dmin ≤
      roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope buffer fuel)
    (hUmax : roundedQuadraticUpper N upperCoefficient upperR0 upperSlope
      buffer 0 ≤ Umax)
    (hreserve : ∀ i, i ≤ fuel → reserve ≤ outerSharpEligiblePairs H X i)
    (hDcut : Dcut ≤ reserve * dmin / 3)
    (hdminPos : 0 < dmin) :
    ∀ i, i ≤ fuel →
      dmin ≤ outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ∧
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤ Umax ∧
      Dcut ≤ outerSharpLowerAvailability H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ∧
      0 ≤ (outerSharpEnvelope H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i).2 - buffer := by
  intro i hi
  have hs := hschedules i hi
  have hlowEndpoint :
      roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope buffer fuel ≤
        roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope buffer i :=
    roundedQuadraticLower_antitone_on hlowerPos hi le_rfl
  have huEndpoint :
      roundedQuadraticUpper N upperCoefficient upperR0 upperSlope buffer i ≤
        roundedQuadraticUpper N upperCoefficient upperR0 upperSlope buffer 0 :=
    roundedQuadraticUpper_antitone_on hupperPos (Nat.zero_le i) hi
  have hd : dmin ≤ outerSharpLowerSchedule H X
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i :=
    hdmin.trans (hlowEndpoint.trans hs.2.1)
  have hu : outerSharpUpperSchedule H X
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤ Umax :=
    hs.1.trans (huEndpoint.trans hUmax)
  have hD : Dcut ≤ outerSharpLowerAvailability H X
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := by
    rw [outerSharpLowerAvailability_eq]
    exact hDcut.trans (Nat.div_le_div_right
      (Nat.mul_le_mul (hreserve i hi) hd))
  have hspos : 0 < outerSharpLowerSchedule H X
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := hdminPos.trans_le hd
  have hnonneg := sharpPairEnvelope_lower_sub_buffer_nonneg_of_lowerSchedule_pos
    (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
    (outerSharpLowerFormula H X) (outerSharpUpperFormula H X) i hspos
  exact ⟨hd, hu, hD, hnonneg⟩

end

end Erdos207
