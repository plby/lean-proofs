/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RoundedOuterQuadraticBarrier

/-!
# Constant-offset quadratic barriers for the outer phase

A constant offset is the useful way to pay for the small error at time zero:
it disappears from every one-step difference.  Consequently the upper
quadratic may use a coefficient slightly below four and the lower quadratic
a coefficient slightly above four.  Those are exactly the favourable signs
in the two deletion-rate comparisons.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

def offsetQuadraticUpper
    (N coefficient R0 slope : ℝ≥0) (offset buffer : ℝ) (i : ℕ) : ℕ :=
  nonnegativeNatCeil
    (quadraticPairBarrier N coefficient R0 slope i + offset + buffer)

def offsetQuadraticLower
    (N coefficient R0 slope : ℝ≥0) (offset buffer : ℝ) (i : ℕ) : ℕ :=
  nonnegativeNatFloor
    (quadraticPairBarrier N coefficient R0 slope i - offset - buffer)

/-- Endpoint inequalities for constant-offset quadratic barriers trap the
exact recursive outer schedules.  The offset is absent from the rate
hypotheses because it cancels in consecutive barrier differences. -/
theorem outerSharpRecursiveSchedules_between_offsetQuadraticBarriers
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ : ℕ) (offset buffer : ℝ) (Kinc fuel : ℕ)
    (N upperCoefficient lowerCoefficient R0 upperSlope lowerSlope : ℝ≥0)
    (a b cNumer cDenom : ℕ)
    (hbufferNonneg : 0 ≤ buffer)
    (hinitialOrder : lower₀ ≤ upper₀)
    (hupperInitial : (upper₀ : ℝ) ≤
      quadraticPairBarrier N upperCoefficient R0 upperSlope 0 + offset)
    (hlowerInitial :
      quadraticPairBarrier N lowerCoefficient R0 lowerSlope 0 - offset ≤
        (lower₀ : ℝ))
    (hupperPos : (fuel : ℝ≥0) * upperSlope < R0)
    (hlowerPos : (fuel : ℝ≥0) * lowerSlope < R0)
    (hb : 0 < b)
    (hcDenom : 0 < cDenom)
    (hlowerEndpointPos : ∀ i, i < fuel →
      0 < offsetQuadraticLower N lowerCoefficient R0 lowerSlope
        offset buffer i)
    (hupperAvailability : ∀ i, i < fuel →
      3 ≤ outerSharpEligiblePairs H X i *
        offsetQuadraticLower N lowerCoefficient R0 lowerSlope
          offset buffer i)
    (hupperLoss : ∀ i, i < fuel →
      a * offsetQuadraticUpper N upperCoefficient R0 upperSlope
          offset buffer i ≤
        b * (3 * offsetQuadraticLower N lowerCoefficient R0 lowerSlope
          offset buffer i - 2 -
            offsetQuadraticUpper N upperCoefficient R0 upperSlope
              offset buffer i))
    (hupperRate : ∀ i, i < fuel →
      ((upperCoefficient * upperSlope *
          (2 * affineSurvivalEnvelope R0 upperSlope i - upperSlope) *
          N⁻¹ ^ 3 : ℝ≥0) : ℝ) ≤
        ((3 * a * offsetQuadraticLower N lowerCoefficient R0 lowerSlope
          offset buffer i : ℕ) : ℝ) /
            (b * outerSharpEligiblePairs H X i : ℕ))
    (heligiblePos : ∀ i, i < fuel →
      0 < outerSharpEligiblePairs H X i)
    (hlowerGap : ∀ i, i < fuel →
      offsetQuadraticUpper N upperCoefficient R0 upperSlope offset buffer i <
        outerSharpEligiblePairs H X i *
          offsetQuadraticLower N lowerCoefficient R0 lowerSlope
            offset buffer i / 3)
    (hlowerScalar : ∀ i, i < fuel →
      cDenom * outerSharpEligiblePairs H X i *
          (offsetQuadraticUpper N upperCoefficient R0 upperSlope
              offset buffer i *
                (2 * offsetQuadraticUpper N upperCoefficient R0 upperSlope
                  offset buffer i) + Kinc) ≤
        cNumer * offsetQuadraticLower N lowerCoefficient R0 lowerSlope
            offset buffer i * (outerSharpEligiblePairs H X i *
            offsetQuadraticLower N lowerCoefficient R0 lowerSlope
              offset buffer i / 3 -
          offsetQuadraticUpper N upperCoefficient R0 upperSlope
            offset buffer i))
    (hlowerRate : ∀ i, i < fuel →
      ((cNumer * offsetQuadraticUpper N upperCoefficient R0 upperSlope
          offset buffer i : ℕ) : ℝ) /
          (cDenom * outerSharpEligiblePairs H X i : ℕ) ≤
        ((lowerCoefficient * lowerSlope *
          (2 * affineSurvivalEnvelope R0 lowerSlope i - lowerSlope) *
          N⁻¹ ^ 3 : ℝ≥0) : ℝ)) :
    ∀ i, i ≤ fuel →
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
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := by
  let upperBarrier : ℕ → ℝ := fun i ↦
    quadraticPairBarrier N upperCoefficient R0 upperSlope i + offset
  let lowerBarrier : ℕ → ℝ := fun i ↦
    quadraticPairBarrier N lowerCoefficient R0 lowerSlope i - offset
  apply sharpRecursiveSchedules_between_barriers_until_of_box_ordered
    (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc fuel
    (outerSharpLowerFormula H X) (outerSharpUpperFormula H X)
    upperBarrier lowerBarrier hbufferNonneg
    (by exact_mod_cast hinitialOrder) hupperInitial hlowerInitial
  · intro i hi hu hd _hdu
    have hu' : outerSharpUpperSchedule H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        offsetQuadraticUpper N upperCoefficient R0 upperSlope
          offset buffer i := by
      simpa only [offsetQuadraticUpper, upperBarrier] using hu
    have hd' : offsetQuadraticLower N lowerCoefficient R0 lowerSlope
        offset buffer i ≤ outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := by
      simpa only [offsetQuadraticLower, lowerBarrier] using hd
    rw [show upperBarrier i - upperBarrier (i + 1) =
        quadraticPairBarrier N upperCoefficient R0 upperSlope i -
          quadraticPairBarrier N upperCoefficient R0 upperSlope (i + 1) by
      dsimp only [upperBarrier]
      ring]
    rw [quadraticPairBarrier_sub_succ hupperPos hi]
    calc
      ((upperCoefficient * upperSlope *
          (2 * affineSurvivalEnvelope R0 upperSlope i - upperSlope) *
          N⁻¹ ^ 3 : ℝ≥0) : ℝ) ≤
          ((3 * a * offsetQuadraticLower N lowerCoefficient R0 lowerSlope
            offset buffer i : ℕ) : ℝ) /
              (b * outerSharpEligiblePairs H X i : ℕ) := hupperRate i hi
      _ ≤ ((3 * a * outerSharpLowerSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i : ℕ) : ℝ) /
              (b * outerSharpEligiblePairs H X i : ℕ) := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Nat.mul_le_mul_left (3 * a) hd'
        · positivity
      _ ≤ sharpScheduledPairUpperRate
          (outerSharpUpperAvailability H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
          (outerSharpLowerSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
          (outerSharpUpperSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i) := by
        apply div_le_sharpScheduledPairUpperRate
        · exact heligiblePos i hi
        · exact hb
        · rw [outerSharpUpperAvailability_eq]
          apply Nat.div_pos
          · exact (hupperAvailability i hi).trans
              (Nat.mul_le_mul_left (outerSharpEligiblePairs H X i)
                (hd'.trans _hdu))
          · norm_num
        · exact three_mul_outerSharpUpperAvailability_le H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
        · calc
        a * outerSharpUpperSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
            a * offsetQuadraticUpper N upperCoefficient R0 upperSlope
              offset buffer i := Nat.mul_le_mul_left a hu'
        _ ≤ b * (3 * offsetQuadraticLower N lowerCoefficient R0 lowerSlope
            offset buffer i - 2 -
              offsetQuadraticUpper N upperCoefficient R0 upperSlope
                offset buffer i) := hupperLoss i hi
        _ ≤ b * (3 * outerSharpLowerSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i - 2 -
            outerSharpUpperSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i) := by
          apply Nat.mul_le_mul_left
          exact (Nat.sub_le_sub_right
            (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 hd') 2)
            (offsetQuadraticUpper N upperCoefficient R0 upperSlope
              offset buffer i)).trans
                (Nat.sub_le_sub_left hu' _)
  · intro i hi hu hd _hdu
    have hu' : outerSharpUpperSchedule H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        offsetQuadraticUpper N upperCoefficient R0 upperSlope
          offset buffer i := by
      simpa only [offsetQuadraticUpper, upperBarrier] using hu
    have hd' : offsetQuadraticLower N lowerCoefficient R0 lowerSlope
        offset buffer i ≤ outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := by
      simpa only [offsetQuadraticLower, lowerBarrier] using hd
    rw [show lowerBarrier i - lowerBarrier (i + 1) =
        quadraticPairBarrier N lowerCoefficient R0 lowerSlope i -
          quadraticPairBarrier N lowerCoefficient R0 lowerSlope (i + 1) by
      dsimp only [lowerBarrier]
      ring]
    rw [quadraticPairBarrier_sub_succ hlowerPos hi]
    have hgap : outerSharpUpperSchedule H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i <
        outerSharpLowerAvailability H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := by
      rw [outerSharpLowerAvailability_eq]
      have hdiv : outerSharpEligiblePairs H X i *
            offsetQuadraticLower N lowerCoefficient R0 lowerSlope
              offset buffer i / 3 ≤
          outerSharpEligiblePairs H X i *
            outerSharpLowerSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i / 3 :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ hd')
      exact hu'.trans_lt ((hlowerGap i hi).trans_le hdiv)
    have hscalar : cDenom * outerSharpEligiblePairs H X i *
          (outerSharpUpperSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i *
                (2 * outerSharpUpperSchedule H X
                  (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i) + Kinc) ≤
        cNumer * outerSharpUpperSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i *
          (outerSharpLowerAvailability H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i -
            outerSharpUpperSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i) := by
      let E := outerSharpEligiblePairs H X i
      let U := offsetQuadraticUpper N upperCoefficient R0 upperSlope
        offset buffer i
      let L := offsetQuadraticLower N lowerCoefficient R0 lowerSlope
        offset buffer i
      let u := outerSharpUpperSchedule H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
      let d := outerSharpLowerSchedule H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
      let D := outerSharpLowerAvailability H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
      have hLpos : 0 < L := hlowerEndpointPos i hi
      have hLd : L ≤ d := by simpa only [L, d] using hd'
      have hduLocal : d ≤ u := by simpa only [d, u] using _hdu
      have hinside : u * (2 * u) + Kinc ≤ U * (2 * U) + Kinc := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul (by simpa only [U] using hu')
            (Nat.mul_le_mul_left 2 (by simpa only [U] using hu')))
          Kinc
      have hDlower : E * L / 3 ≤ D := by
        change outerSharpEligiblePairs H X i * L / 3 ≤
          outerSharpLowerAvailability H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
        rw [outerSharpLowerAvailability_eq]
        exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (by
          simpa only [L] using hd'))
      have hwidth : E * L / 3 - U ≤ D - u :=
        (Nat.sub_le_sub_right hDlower U).trans
          (Nat.sub_le_sub_left (by simpa only [U] using hu') D)
      have hLu : L ≤ u := hLd.trans hduLocal
      calc
        cDenom * E * (u * (2 * u) + Kinc) ≤
            cDenom * E * (U * (2 * U) + Kinc) :=
          Nat.mul_le_mul_left (cDenom * E) hinside
        _ ≤ cNumer * L * (E * L / 3 - U) := hlowerScalar i hi
        _ ≤ cNumer * u * (E * L / 3 - U) := by
          exact Nat.mul_le_mul_right (E * L / 3 - U)
            (Nat.mul_le_mul_left cNumer hLu)
        _ ≤ cNumer * u * (D - u) :=
          Nat.mul_le_mul_left (cNumer * u) hwidth
    calc
      sharpScheduledPairLowerRate
          (outerSharpLowerAvailability H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
          (outerSharpUpperSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i) Kinc ≤
        ((cNumer * outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i : ℕ) : ℝ) /
            (cDenom * outerSharpEligiblePairs H X i : ℕ) :=
        sharpScheduledPairLowerRate_le_div_ratio
          (outerSharpEligiblePairs H X i) cNumer cDenom
          (outerSharpLowerAvailability H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
          (outerSharpUpperSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
          Kinc (heligiblePos i hi) hcDenom hgap hscalar
      _ ≤ ((cNumer * offsetQuadraticUpper N upperCoefficient R0 upperSlope
          offset buffer i : ℕ) : ℝ) /
            (cDenom * outerSharpEligiblePairs H X i : ℕ) := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Nat.mul_le_mul_left cNumer hu'
        · positivity
      _ ≤ ((lowerCoefficient * lowerSlope *
          (2 * affineSurvivalEnvelope R0 lowerSlope i - lowerSlope) *
          N⁻¹ ^ 3 : ℝ≥0) : ℝ) := hlowerRate i hi
  · intro i hi hu hd hdu
    have hu' : outerSharpUpperSchedule H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        offsetQuadraticUpper N upperCoefficient R0 upperSlope
          offset buffer i := by
      simpa only [offsetQuadraticUpper, upperBarrier] using hu
    have hd' : offsetQuadraticLower N lowerCoefficient R0 lowerSlope
        offset buffer i ≤ outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := by
      simpa only [offsetQuadraticLower, lowerBarrier] using hd
    apply outerSharpScheduledPairUpperRate_le_lowerRate H X
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
    · rw [outerSharpUpperAvailability_eq]
      apply Nat.div_pos
      · exact (hupperAvailability i hi).trans
          (Nat.mul_le_mul_left (outerSharpEligiblePairs H X i)
            (hd'.trans hdu))
      · norm_num
    · rw [outerSharpLowerAvailability_eq]
      have hdiv : outerSharpEligiblePairs H X i *
            offsetQuadraticLower N lowerCoefficient R0 lowerSlope
              offset buffer i / 3 ≤
          outerSharpEligiblePairs H X i *
            outerSharpLowerSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i / 3 :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ hd')
      exact (show outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i <
          outerSharpLowerAvailability H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i from
        (by
          exact hu'.trans_lt ((hlowerGap i hi).trans_le hdiv)))
    · exact hdu

end

end Erdos207
