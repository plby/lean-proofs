/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CubicSurvivalCancellation
import ErdosProblems.Erdos207.OuterOnlyRecursiveSharpSchedule

/-!
# Cubic cancellation for the recursive outer-only schedule

This file specializes the abstract fractional-envelope estimate to the exact
lower/upper availability formulas used by the sharp outer-only process.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def outerSharpEligiblePairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (_X : Finset V) (i : ℕ) : ℕ :=
  Nat.choose (Fintype.card V) 2 - 3 * i -
    (graphEdges H).card

def outerSharpAllPairs (V : Type*) [Fintype V] (i : ℕ) : ℕ :=
  Nat.choose (Fintype.card V) 2 - 3 * i

lemma three_mul_outerSharpUpperAvailability_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc i : ℕ) :
    3 * outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i ≤
      outerSharpEligiblePairs H X i *
        outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i := by
  rw [outerSharpUpperAvailability_eq]
  exact Nat.mul_div_le _ _

lemma outerSharpEligible_mul_lower_le_five_mul_availability
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc i : ℕ)
    (hthree : 3 ≤ outerSharpEligiblePairs H X i *
      outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i) :
    outerSharpEligiblePairs H X i *
        outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i ≤
      5 * outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i := by
  rw [outerSharpLowerAvailability_eq]
  exact le_five_mul_div_three hthree

lemma outerSharpLowerAvailability_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc i : ℕ)
    (hthree : 3 ≤ outerSharpEligiblePairs H X i *
      outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i) :
    0 < outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i := by
  rw [outerSharpLowerAvailability_eq]
  apply Nat.div_pos
  · simpa only [outerSharpEligiblePairs] using hthree
  · norm_num

/-- The same affine envelope that controls the retrospective point term also
controls the total survival product of the recursive sharp schedule. -/
theorem cumulativeSurvival_outerSharpRecursive_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc fuel K : ℕ)
    {R0 slope : ℝ≥0}
    (hMpos : ∀ i, i < fuel →
      0 < outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i)
    (henvelopePos : (fuel : ℝ≥0) * slope < R0)
    (hallEnvelope : ∀ i, i < fuel →
      (outerSharpEligiblePairs H X i : ℝ≥0) ≤
        affineSurvivalEnvelope R0 slope i)
    (hratio : ∀ i, i < fuel →
      slope * (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i : ℕ) ≤
        3 * (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i -
          K : ℕ)) :
    cumulativeSurvival
        (boundedSharpSurvivalSchedule fuel
          (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc)
          (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc) K)
        fuel ≤ affineSurvivalEnvelope R0 slope fuel / R0 := by
  let R : ℕ → ℝ≥0 := affineSurvivalEnvelope R0 slope
  have hR : ∀ i, i ≤ fuel → 0 < R i := by
    intro i hi
    exact affineSurvivalEnvelope_pos henvelopePos hi
  have htheta : ∀ i, i < fuel →
      boundedSharpSurvivalSchedule fuel
          (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc)
          (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc) K i ≤
        R (i + 1) / R i :=
    boundedSharpSurvivalSchedule_le_nnreal_envelope_ratio
      (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc)
      (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc) K R
      hMpos hR
      (fun i _hi ↦ affineSurvivalEnvelope_antitone R0 slope
        (Nat.le_succ i))
      (fun i hi ↦ by
        rw [affineSurvivalEnvelope_sub_succ (le_of_lt henvelopePos) hi]
        exact affineEnvelope_loss_of_three_mul (hallEnvelope i hi)
          (three_mul_outerSharpUpperAvailability_le H X upper₀ lower₀
            buffer Kinc i)
          (hratio i hi))
  simpa only [R, affineSurvivalEnvelope, Nat.cast_zero, zero_mul,
    tsub_zero] using
    cumulativeSurvival_le_envelope_ratio
      (boundedSharpSurvivalSchedule fuel
        (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc)
        (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc) K)
      R hR htheta fuel le_rfl

/-- The recursive sharp schedule has the inverse-ambient point-transfer
bound once its natural pair-count comparisons are supplied.  All divisions
by three and the cumulative survival product are discharged here. -/
theorem transferPointWeight_outerSharpRecursive_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc fuel K : ℕ)
    {R0 slope Cfactor Q A B : ℝ≥0}
    (hcard : 0 < Fintype.card V)
    (hfuel : fuel ≤ Fintype.card V ^ 2)
    (hfactor : ∀ i, i < fuel →
      (boundedSharpSurvivalTheta
        (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i)
        (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i)
        (3 * K) ^ (3 * K))⁻¹ ≤ Cfactor)
    (hMpos : ∀ i, i < fuel →
      0 < outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i)
    (henvelopePos : (fuel : ℝ≥0) * slope < R0)
    (hallEnvelope : ∀ i, i < fuel →
      (outerSharpEligiblePairs H X i : ℝ≥0) ≤
        affineSurvivalEnvelope R0 slope i)
    (hratio : ∀ i, i < fuel →
      slope * (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i : ℕ) ≤
        3 * (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i -
          3 * K : ℕ))
    (hthree : ∀ i, i < fuel →
      3 ≤ outerSharpEligiblePairs H X i *
        outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i)
    (henvelopeEligible : ∀ i, i < fuel →
      affineSurvivalEnvelope R0 slope i ≤
        A * (outerSharpEligiblePairs H X i : ℕ))
    (hpairScale : ∀ i, i < fuel →
      ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 ≤
        B * (Fintype.card V : ℝ≥0) ^ 3 *
          (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i : ℕ))
    (hquadratic : (Fintype.card V : ℝ≥0) ^ 2 ≤ Q * R0) :
    transferPointWeight
        (boundedSharpSurvivalSchedule fuel
          (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc)
          (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc)
          (3 * K))
        (boundedSharpTransferSchedule fuel
          (outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc)
          (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc)
          (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc)
          (3 * K)) fuel ≤
      (Cfactor * (Q ^ 3 * (5 * A ^ 3 * B))) *
        (Fintype.card V : ℝ≥0)⁻¹ := by
  apply transferPointWeight_boundedSharp_le_of_affineEnvelope
    hcard hfuel hfactor hMpos henvelopePos
  · intro i hi
    apply affineEnvelope_loss_of_three_mul (hallEnvelope i hi)
      (three_mul_outerSharpUpperAvailability_le H X upper₀ lower₀ buffer Kinc i)
      (hratio i hi)
  · exact hquadratic
  · intro i hi
    apply inv_mul_cube_le_of_quadratic_pairScale
      (N := (Fintype.card V : ℝ≥0))
      (D := (outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i : ℝ≥0))
      (R := affineSurvivalEnvelope R0 slope i)
      (P := (outerSharpEligiblePairs H X i : ℝ≥0))
      (d := (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i : ℝ≥0))
      (C := 5) (A := A) (B := B)
    · have hprod := hthree i hi
      have hd : 0 < outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i := by
        apply pos_of_mul_pos_right (lt_of_lt_of_le (by norm_num) hprod)
        exact Nat.zero_le _
      exact_mod_cast hd
    · exact_mod_cast outerSharpLowerAvailability_pos H X upper₀ lower₀
        buffer Kinc i (hthree i hi)
    · exact_mod_cast outerSharpEligible_mul_lower_le_five_mul_availability
        H X upper₀ lower₀ buffer Kinc i (hthree i hi)
    · exact henvelopeEligible i hi
    · exact hpairScale i hi

/-- Fixed-pattern specialization: if every effective pair loss is at most
half of the upper availability, the local reciprocal factor is the constant
`2^(3*K)`. -/
theorem transferPointWeight_outerSharpRecursive_le_of_half
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc fuel K : ℕ)
    {R0 slope Q A B : ℝ≥0}
    (hcard : 0 < Fintype.card V)
    (hfuel : fuel ≤ Fintype.card V ^ 2)
    (hMpos : ∀ i, i < fuel →
      0 < outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i)
    (hhalf : ∀ i, i < fuel →
      2 * (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i - 3 * K) ≤
        outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i)
    (henvelopePos : (fuel : ℝ≥0) * slope < R0)
    (hallEnvelope : ∀ i, i < fuel →
      (outerSharpEligiblePairs H X i : ℝ≥0) ≤
        affineSurvivalEnvelope R0 slope i)
    (hratio : ∀ i, i < fuel →
      slope * (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i : ℕ) ≤
        3 * (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i -
          3 * K : ℕ))
    (hthree : ∀ i, i < fuel →
      3 ≤ outerSharpEligiblePairs H X i *
        outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i)
    (henvelopeEligible : ∀ i, i < fuel →
      affineSurvivalEnvelope R0 slope i ≤
        A * (outerSharpEligiblePairs H X i : ℕ))
    (hpairScale : ∀ i, i < fuel →
      ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 ≤
        B * (Fintype.card V : ℝ≥0) ^ 3 *
          (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i : ℕ))
    (hquadratic : (Fintype.card V : ℝ≥0) ^ 2 ≤ Q * R0) :
    transferPointWeight
        (boundedSharpSurvivalSchedule fuel
          (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc)
          (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc)
          (3 * K))
        (boundedSharpTransferSchedule fuel
          (outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc)
          (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc)
          (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc)
          (3 * K)) fuel ≤
      (((2 : ℝ≥0) ^ (3 * K)) * (Q ^ 3 * (5 * A ^ 3 * B))) *
        (Fintype.card V : ℝ≥0)⁻¹ := by
  apply transferPointWeight_outerSharpRecursive_le H X upper₀ lower₀ buffer
    Kinc fuel K hcard hfuel
    (Cfactor := (2 : ℝ≥0) ^ (3 * K))
    (fun i hi ↦ inv_pow_boundedSharpSurvivalTheta_le
      (hMpos i hi) (hhalf i hi)) hMpos
    henvelopePos hallEnvelope hratio hthree henvelopeEligible hpairScale
    hquadratic

end

end Erdos207
