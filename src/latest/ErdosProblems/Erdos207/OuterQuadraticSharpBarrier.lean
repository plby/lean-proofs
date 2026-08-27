/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.QuadraticPairBarrier
import ErdosProblems.Erdos207.SharpRateAlgebra
import ErdosProblems.Erdos207.OuterSharpCubicSchedule

/-!
# Quadratic barriers for the recursive outer-only schedule

This is the scalar bridge between the exact natural-number availability
formulas and the real quadratic sub- and super-solutions.  All divisions and
rounding remain exposed as cross-multiplied hypotheses, ready for the power
hierarchy arithmetic.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

/-- For the exact outer availability formulas, the conservative lower rate
dominates the conservative upper rate whenever the natural lower schedule is
at most the upper schedule and both denominators are positive. -/
lemma outerSharpScheduledPairUpperRate_le_lowerRate
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc i : ℕ)
    (hM : 0 < outerSharpUpperAvailability H X
      upper₀ lower₀ buffer Kinc i)
    (hgap : outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i <
      outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i)
    (hdu : outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i ≤
      outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i) :
    sharpScheduledPairUpperRate
        (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i)
        (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i)
        (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i) ≤
      sharpScheduledPairLowerRate
        (outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i)
        (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i)
        Kinc := by
  let d := outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i
  let u := outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i
  let D := outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i
  let M := outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i
  have hDM : D ≤ M := by
    change outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i ≤
      outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i
    rw [outerSharpLowerAvailability_eq, outerSharpUpperAvailability_eq]
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul_left _ hdu
  have hloss : 3 * d - 2 - u ≤ 2 * u := by omega
  have hnum : d * (3 * d - 2 - u) ≤ u * (2 * u) :=
    Nat.mul_le_mul hdu hloss
  have hden : D - u ≤ M := (Nat.sub_le D u).trans hDM
  apply sharpScheduledPairUpperRate_le_lowerRate M D d u Kinc hM hgap
  calc
    d * (3 * d - 2 - u) * (D - u) ≤
        (u * (2 * u)) * (D - u) := Nat.mul_le_mul_right _ hnum
    _ ≤ (u * (2 * u)) * M := Nat.mul_le_mul_left _ hden
    _ ≤ (u * (2 * u) + Kinc) * M :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    _ = M * (u * (2 * u) + Kinc) := Nat.mul_comm _ _

/-- Cross-multiplied quadratic sub- and super-solution estimates trap the
exact recursive outer-only pair schedules up to the stopping time. -/
theorem outerSharpRecursiveSchedules_between_quadraticBarriers
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ : ℕ) (buffer : ℝ) (Kinc fuel : ℕ)
    (N upperCoefficient lowerCoefficient upperR0 lowerR0
      upperSlope lowerSlope : ℝ≥0)
    (a b cNumer cDenom : ℕ)
    (hbufferNonneg : 0 ≤ buffer)
    (hinitialOrder : lower₀ ≤ upper₀)
    (hupperInitial : (upper₀ : ℝ) ≤
      quadraticPairBarrier N upperCoefficient upperR0 upperSlope 0)
    (hlowerInitial :
      quadraticPairBarrier N lowerCoefficient lowerR0 lowerSlope 0 ≤
        (lower₀ : ℝ))
    (hupperPos : (fuel : ℝ≥0) * upperSlope < upperR0)
    (hlowerPos : (fuel : ℝ≥0) * lowerSlope < lowerR0)
    (hb : 0 < b)
    (hcDenom : 0 < cDenom)
    (hupperAvailabilityPos : ∀ i, i < fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        nonnegativeNatCeil
          (quadraticPairBarrier N upperCoefficient upperR0 upperSlope i +
            buffer) →
      nonnegativeNatFloor
          (quadraticPairBarrier N lowerCoefficient lowerR0 lowerSlope i -
            buffer) ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      0 < outerSharpUpperAvailability H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
    (hupperLoss : ∀ i, i < fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        nonnegativeNatCeil
          (quadraticPairBarrier N upperCoefficient upperR0 upperSlope i +
            buffer) →
      nonnegativeNatFloor
          (quadraticPairBarrier N lowerCoefficient lowerR0 lowerSlope i -
            buffer) ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      a * outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        b * (3 * outerSharpLowerSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i - 2 -
          outerSharpUpperSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i))
    (hupperRate : ∀ i, i < fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        nonnegativeNatCeil
          (quadraticPairBarrier N upperCoefficient upperR0 upperSlope i +
            buffer) →
      nonnegativeNatFloor
          (quadraticPairBarrier N lowerCoefficient lowerR0 lowerSlope i -
            buffer) ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      ((upperCoefficient * upperSlope *
          (2 * affineSurvivalEnvelope upperR0 upperSlope i - upperSlope) *
          N⁻¹ ^ 3 : ℝ≥0) : ℝ) ≤
        ((3 * a * outerSharpLowerSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i : ℕ) : ℝ) /
          (b * outerSharpEligiblePairs H X i : ℕ))
    (heligiblePos : ∀ i, i < fuel →
      0 < outerSharpEligiblePairs H X i)
    (hlowerGap : ∀ i, i < fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        nonnegativeNatCeil
          (quadraticPairBarrier N upperCoefficient upperR0 upperSlope i +
            buffer) →
      nonnegativeNatFloor
          (quadraticPairBarrier N lowerCoefficient lowerR0 lowerSlope i -
            buffer) ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i <
        outerSharpLowerAvailability H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
    (hlowerScalar : ∀ i, i < fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        nonnegativeNatCeil
          (quadraticPairBarrier N upperCoefficient upperR0 upperSlope i +
            buffer) →
      nonnegativeNatFloor
          (quadraticPairBarrier N lowerCoefficient lowerR0 lowerSlope i -
            buffer) ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      cDenom * outerSharpEligiblePairs H X i *
          (outerSharpUpperSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i *
                (2 * outerSharpUpperSchedule H X
                  (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i) +
            Kinc) ≤
        cNumer * outerSharpUpperSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i *
          (outerSharpLowerAvailability H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i -
            outerSharpUpperSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i))
    (hlowerRate : ∀ i, i < fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        nonnegativeNatCeil
          (quadraticPairBarrier N upperCoefficient upperR0 upperSlope i +
            buffer) →
      nonnegativeNatFloor
          (quadraticPairBarrier N lowerCoefficient lowerR0 lowerSlope i -
            buffer) ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i →
      ((cNumer * outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i : ℕ) : ℝ) /
          (cDenom * outerSharpEligiblePairs H X i : ℕ) ≤
        ((lowerCoefficient * lowerSlope *
          (2 * affineSurvivalEnvelope lowerR0 lowerSlope i - lowerSlope) *
          N⁻¹ ^ 3 : ℝ≥0) : ℝ)) :
    ∀ i, i ≤ fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        nonnegativeNatCeil
          (quadraticPairBarrier N upperCoefficient upperR0 upperSlope i +
            buffer) ∧
      nonnegativeNatFloor
          (quadraticPairBarrier N lowerCoefficient lowerR0 lowerSlope i -
            buffer) ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ∧
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := by
  apply sharpRecursiveSchedules_between_barriers_until_of_box_ordered
    (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc fuel
    (outerSharpLowerFormula H X) (outerSharpUpperFormula H X)
    (quadraticPairBarrier N upperCoefficient upperR0 upperSlope)
    (quadraticPairBarrier N lowerCoefficient lowerR0 lowerSlope)
    hbufferNonneg (by exact_mod_cast hinitialOrder) hupperInitial hlowerInitial
  · intro i hi hu hd hdu
    rw [quadraticPairBarrier_sub_succ hupperPos hi]
    apply (hupperRate i hi hu hd hdu).trans
    apply div_le_sharpScheduledPairUpperRate
    · exact heligiblePos i hi
    · exact hb
    · exact hupperAvailabilityPos i hi hu hd hdu
    · exact three_mul_outerSharpUpperAvailability_le H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
    · exact hupperLoss i hi hu hd hdu
  · intro i hi hu hd hdu
    rw [quadraticPairBarrier_sub_succ hlowerPos hi]
    exact (sharpScheduledPairLowerRate_le_div_ratio
      (outerSharpEligiblePairs H X i) cNumer cDenom
      (outerSharpLowerAvailability H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
      (outerSharpUpperSchedule H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
      Kinc (heligiblePos i hi) hcDenom (hlowerGap i hi hu hd hdu)
        (hlowerScalar i hi hu hd hdu)).trans
        (hlowerRate i hi hu hd hdu)
  · intro i hi hu hd hdu
    exact outerSharpScheduledPairUpperRate_le_lowerRate H X
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
      (hupperAvailabilityPos i hi hu hd hdu)
      (hlowerGap i hi hu hd hdu) hdu

end

end Erdos207
