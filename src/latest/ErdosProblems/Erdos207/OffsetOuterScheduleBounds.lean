/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOffsetOuterCorridor

/-!
# Uniform consequences of a constant-offset outer corridor

The fine comparison theorem gives time-dependent barriers.  This file turns
their endpoint values into the uniform floor, ceiling, and availability
certificate consumed by the recursive initial-product law.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

lemma offsetQuadraticUpper_antitone_on
    {N coefficient R0 slope : ℝ≥0} {offset buffer : ℝ} {fuel i j : ℕ}
    (hpos : (fuel : ℝ≥0) * slope < R0) (hij : i ≤ j) (hj : j ≤ fuel) :
    offsetQuadraticUpper N coefficient R0 slope offset buffer j ≤
      offsetQuadraticUpper N coefficient R0 slope offset buffer i := by
  unfold offsetQuadraticUpper nonnegativeNatCeil
  apply Nat.ceil_mono
  apply max_le_max_left
  have hbar := quadraticPairBarrier_antitone_on
    (N := N) (coefficient := coefficient) hpos hij hj
  linarith

lemma offsetQuadraticLower_antitone_on
    {N coefficient R0 slope : ℝ≥0} {offset buffer : ℝ} {fuel i j : ℕ}
    (hpos : (fuel : ℝ≥0) * slope < R0) (hij : i ≤ j) (hj : j ≤ fuel) :
    offsetQuadraticLower N coefficient R0 slope offset buffer j ≤
      offsetQuadraticLower N coefficient R0 slope offset buffer i := by
  unfold offsetQuadraticLower nonnegativeNatFloor
  apply Nat.floor_mono
  apply max_le_max_left
  have hbar := quadraticPairBarrier_antitone_on
    (N := N) (coefficient := coefficient) hpos hij hj
  linarith

/-- A constant-offset corridor and its endpoint estimates imply the uniform
certificate required by `outerSharpRecursive_absorberInitialProductLaw`. -/
theorem outerSharpUniformBounds_of_offsetCorridor
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ : ℕ) (offset buffer : ℝ) (Kinc fuel : ℕ)
    (N upperCoefficient lowerCoefficient R0 upperSlope lowerSlope : ℝ≥0)
    (dmin Umax reserve Dcut : ℕ)
    (hupperPos : (fuel : ℝ≥0) * upperSlope < R0)
    (hlowerPos : (fuel : ℝ≥0) * lowerSlope < R0)
    (hschedules : ∀ i, i ≤ fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        offsetQuadraticUpper N upperCoefficient R0 upperSlope
          offset buffer i ∧
      offsetQuadraticLower N lowerCoefficient R0 lowerSlope
          offset buffer i ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ∧
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
    (hdmin : dmin ≤ offsetQuadraticLower N lowerCoefficient R0 lowerSlope
      offset buffer fuel)
    (hUmax : offsetQuadraticUpper N upperCoefficient R0 upperSlope
      offset buffer 0 ≤ Umax)
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
      offsetQuadraticLower N lowerCoefficient R0 lowerSlope
          offset buffer fuel ≤
        offsetQuadraticLower N lowerCoefficient R0 lowerSlope
          offset buffer i :=
    offsetQuadraticLower_antitone_on hlowerPos hi le_rfl
  have huEndpoint :
      offsetQuadraticUpper N upperCoefficient R0 upperSlope
          offset buffer i ≤
        offsetQuadraticUpper N upperCoefficient R0 upperSlope
          offset buffer 0 :=
    offsetQuadraticUpper_antitone_on hupperPos (Nat.zero_le i) hi
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
