/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterQuadraticSharpBarrier

/-!
# Rounded endpoint criteria for the outer quadratic barriers

All self-referential schedule values are eliminated here.  It is enough to
verify natural inequalities at the explicit floor and ceiling endpoints of
the quadratic corridor.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

def roundedQuadraticUpper
    (N coefficient R0 slope : ℝ≥0) (buffer : ℝ) (i : ℕ) : ℕ :=
  nonnegativeNatCeil (quadraticPairBarrier N coefficient R0 slope i + buffer)

def roundedQuadraticLower
    (N coefficient R0 slope : ℝ≥0) (buffer : ℝ) (i : ℕ) : ℕ :=
  nonnegativeNatFloor (quadraticPairBarrier N coefficient R0 slope i - buffer)

/-- Endpoint inequalities for a rounded quadratic corridor imply the exact
recursive outer schedule bounds and preserve lower-before-upper ordering. -/
theorem outerSharpRecursiveSchedules_between_roundedQuadraticBarriers
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
    (hlowerEndpointPos : ∀ i, i < fuel →
      0 < roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope buffer i)
    (hupperAvailability : ∀ i, i < fuel →
      3 ≤ outerSharpEligiblePairs H X i *
        roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope buffer i)
    (hupperLoss : ∀ i, i < fuel →
      a * roundedQuadraticUpper N upperCoefficient upperR0 upperSlope buffer i ≤
        b * (3 * roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope
          buffer i - 2 -
            roundedQuadraticUpper N upperCoefficient upperR0 upperSlope
              buffer i))
    (hupperRate : ∀ i, i < fuel →
      ((upperCoefficient * upperSlope *
          (2 * affineSurvivalEnvelope upperR0 upperSlope i - upperSlope) *
          N⁻¹ ^ 3 : ℝ≥0) : ℝ) ≤
        ((3 * a * roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope
          buffer i : ℕ) : ℝ) /
            (b * outerSharpEligiblePairs H X i : ℕ))
    (heligiblePos : ∀ i, i < fuel →
      0 < outerSharpEligiblePairs H X i)
    (hlowerGap : ∀ i, i < fuel →
      roundedQuadraticUpper N upperCoefficient upperR0 upperSlope buffer i <
        outerSharpEligiblePairs H X i *
          roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope buffer i /
            3)
    (hlowerScalar : ∀ i, i < fuel →
      cDenom * outerSharpEligiblePairs H X i *
          (2 * roundedQuadraticUpper N upperCoefficient upperR0 upperSlope
              buffer i + Kinc) ≤
        cNumer * (outerSharpEligiblePairs H X i *
            roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope
              buffer i / 3 -
          roundedQuadraticUpper N upperCoefficient upperR0 upperSlope
            buffer i))
    (hlowerRate : ∀ i, i < fuel →
      ((cNumer * roundedQuadraticUpper N upperCoefficient upperR0 upperSlope
          buffer i : ℕ) : ℝ) /
          (cDenom * outerSharpEligiblePairs H X i : ℕ) ≤
        ((lowerCoefficient * lowerSlope *
          (2 * affineSurvivalEnvelope lowerR0 lowerSlope i - lowerSlope) *
          N⁻¹ ^ 3 : ℝ≥0) : ℝ)) :
    ∀ i, i ≤ fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        roundedQuadraticUpper N upperCoefficient upperR0 upperSlope buffer i ∧
      roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope buffer i ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ∧
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := by
  apply outerSharpRecursiveSchedules_between_quadraticBarriers H X
    upper₀ lower₀ buffer Kinc fuel N upperCoefficient lowerCoefficient
    upperR0 lowerR0 upperSlope lowerSlope a b cNumer cDenom hbufferNonneg
    hinitialOrder hupperInitial hlowerInitial hupperPos hlowerPos hb hcDenom
  · intro i hi hu hd hdu
    rw [outerSharpUpperAvailability_eq]
    apply Nat.div_pos
    · exact (hupperAvailability i hi).trans
        (Nat.mul_le_mul_left (outerSharpEligiblePairs H X i) (hd.trans hdu))
    · norm_num
  · intro i hi hu hd _hdu
    calc
      a * outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
          a * roundedQuadraticUpper N upperCoefficient upperR0 upperSlope
            buffer i := Nat.mul_le_mul_left a hu
      _ ≤ b * (3 * roundedQuadraticLower N lowerCoefficient lowerR0
          lowerSlope buffer i - 2 - roundedQuadraticUpper N upperCoefficient
            upperR0 upperSlope buffer i) := hupperLoss i hi
      _ ≤ b * (3 * outerSharpLowerSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i - 2 -
          outerSharpUpperSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i) := by
        apply Nat.mul_le_mul_left
        exact (Nat.sub_le_sub_right
          (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 hd) 2)
          (roundedQuadraticUpper N upperCoefficient upperR0 upperSlope buffer i)).trans
            (Nat.sub_le_sub_left hu
              (3 * outerSharpLowerSchedule H X
                (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i - 2))
  · intro i hi _hu hd _hdu
    apply (hupperRate i hi).trans
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Nat.mul_le_mul_left (3 * a) hd
    · positivity
  · exact heligiblePos
  · intro i hi hu hd _hdu
    rw [outerSharpLowerAvailability_eq]
    have hdiv : outerSharpEligiblePairs H X i *
          roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope buffer i /
            3 ≤
        outerSharpEligiblePairs H X i *
          outerSharpLowerSchedule H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i / 3 :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _ hd)
    exact hu.trans_lt ((hlowerGap i hi).trans_le hdiv)
  · intro i hi hu hd hdu
    let E := outerSharpEligiblePairs H X i
    let U := roundedQuadraticUpper N upperCoefficient upperR0 upperSlope buffer i
    let L := roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope buffer i
    let u := outerSharpUpperSchedule H X
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
    let d := outerSharpLowerSchedule H X
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
    let D := outerSharpLowerAvailability H X
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
    have hLpos : 0 < L := hlowerEndpointPos i hi
    have huOne : 1 ≤ u := hLpos.trans_le (hd.trans hdu)
    have hinside : u * (2 * u) + Kinc ≤ u * (2 * U + Kinc) := by
      have hquad : u * (2 * u) ≤ u * (2 * U) := by
        exact Nat.mul_le_mul_left u (Nat.mul_le_mul_left 2 hu)
      have hK : Kinc ≤ u * Kinc := by
        simpa only [one_mul] using Nat.mul_le_mul_right Kinc huOne
      calc
        u * (2 * u) + Kinc ≤ u * (2 * U) + u * Kinc :=
          Nat.add_le_add hquad hK
        _ = u * (2 * U + Kinc) := by ring
    have hDlower : E * L / 3 ≤ D := by
      change outerSharpEligiblePairs H X i *
          roundedQuadraticLower N lowerCoefficient lowerR0 lowerSlope buffer i /
          3 ≤ outerSharpLowerAvailability H X
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
      rw [outerSharpLowerAvailability_eq]
      exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hd)
    have hwidth : E * L / 3 - U ≤ D - u :=
      (Nat.sub_le_sub_right hDlower U).trans (Nat.sub_le_sub_left hu D)
    calc
      cDenom * E * (u * (2 * u) + Kinc) ≤
          cDenom * E * (u * (2 * U + Kinc)) :=
        Nat.mul_le_mul_left (cDenom * E) hinside
      _ = u * (cDenom * E * (2 * U + Kinc)) := by ring
      _ ≤ u * (cNumer * (E * L / 3 - U)) :=
        Nat.mul_le_mul_left u (hlowerScalar i hi)
      _ = cNumer * u * (E * L / 3 - U) := by ring
      _ ≤ cNumer * u * (D - u) :=
        Nat.mul_le_mul_left (cNumer * u) hwidth
  · intro i hi hu _hd _hdu
    apply (show ((cNumer * outerSharpUpperSchedule H X
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i : ℕ) : ℝ) /
          (cDenom * outerSharpEligiblePairs H X i : ℕ) ≤
        ((cNumer * roundedQuadraticUpper N upperCoefficient upperR0 upperSlope
          buffer i : ℕ) : ℝ) /
          (cDenom * outerSharpEligiblePairs H X i : ℕ) by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast Nat.mul_le_mul_left cNumer hu
      · positivity).trans (hlowerRate i hi)

end

end Erdos207
