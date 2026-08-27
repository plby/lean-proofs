/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RoundedOuterQuadraticBarrier

/-!
# Perturbed affine pair-budget envelopes

The usable long-phase barriers have slopes `3 - rho` and `3 + rho`.
Consequently they differ from the exact three-pairs-per-step budget by the
explicit error `i * rho`; choosing `rho` on the scale of the terminal budget
absorbs all rounding while keeping the terminal barriers comparable.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

def perturbedOuterUpperR0
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) : ℝ≥0 :=
  (outerSharpEligiblePairs H X 0 : ℕ)

def perturbedOuterLowerR0
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) : ℝ≥0 :=
  (outerSharpEligiblePairs H X 0 : ℕ)

def perturbedOuterUpperSlope (rho : ℝ≥0) : ℝ≥0 := 3 - rho
def perturbedOuterLowerSlope (rho : ℝ≥0) : ℝ≥0 := 3 + rho

lemma perturbedOuterUpperEnvelope_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (rho : ℝ≥0) (i : ℕ)
    (hrho : rho ≤ 3)
    (hi : 3 * i ≤ outerSharpEligiblePairs H X 0) :
    affineSurvivalEnvelope (perturbedOuterUpperR0 H X)
        (perturbedOuterUpperSlope rho) i =
      (outerSharpEligiblePairs H X i : ℕ) + (i : ℝ≥0) * rho := by
  have hiNN : (3 : ℝ≥0) * (i : ℝ≥0) ≤
      (outerSharpEligiblePairs H X 0 : ℕ) := by
    exact_mod_cast hi
  have hsub : (i : ℝ≥0) * perturbedOuterUpperSlope rho ≤
      perturbedOuterUpperR0 H X := by
    calc
      (i : ℝ≥0) * perturbedOuterUpperSlope rho ≤
          (i : ℝ≥0) * 3 := by
        exact mul_le_mul_of_nonneg_left (tsub_le_self) zero_le
      _ = 3 * (i : ℝ≥0) := mul_comm _ _
      _ ≤ perturbedOuterUpperR0 H X := by
        simpa only [perturbedOuterUpperR0] using hiNN
  apply NNReal.eq
  unfold affineSurvivalEnvelope
  rw [NNReal.coe_sub hsub]
  unfold perturbedOuterUpperSlope perturbedOuterUpperR0
  have heligible : outerSharpEligiblePairs H X i =
      outerSharpEligiblePairs H X 0 - 3 * i := by
    unfold outerSharpEligiblePairs
    omega
  rw [heligible]
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast]
  rw [NNReal.coe_sub hrho]
  rw [Nat.cast_sub hi]
  push_cast
  ring

lemma perturbedOuterLowerEnvelope_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (rho : ℝ≥0) (i : ℕ)
    (hpos : (i : ℝ≥0) * perturbedOuterLowerSlope rho ≤
      perturbedOuterLowerR0 H X) :
    affineSurvivalEnvelope (perturbedOuterLowerR0 H X)
        (perturbedOuterLowerSlope rho) i =
      (outerSharpEligiblePairs H X i : ℕ) - (i : ℝ≥0) * rho := by
  have hiNN : (3 : ℝ≥0) * (i : ℝ≥0) ≤
      (outerSharpEligiblePairs H X 0 : ℕ) := by
    calc
      (3 : ℝ≥0) * i ≤ i * (3 + rho) := by
        rw [mul_comm (3 : ℝ≥0) i]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le) zero_le
      _ ≤ (outerSharpEligiblePairs H X 0 : ℕ) := by
        simpa only [perturbedOuterLowerSlope, perturbedOuterLowerR0] using hpos
  have hiNat : 3 * i ≤ outerSharpEligiblePairs H X 0 := by
    exact_mod_cast hiNN
  have heligible : outerSharpEligiblePairs H X i =
      outerSharpEligiblePairs H X 0 - 3 * i := by
    unfold outerSharpEligiblePairs
    omega
  have hrhoTerm : (i : ℝ≥0) * rho ≤
      (outerSharpEligiblePairs H X i : ℕ) := by
    rw [heligible]
    have hcast : ((outerSharpEligiblePairs H X 0 - 3 * i : ℕ) : ℝ≥0) =
        (outerSharpEligiblePairs H X 0 : ℕ) - (3 * i : ℕ) := by
      have hthreeNN : ((3 * i : ℕ) : ℝ≥0) ≤
          (outerSharpEligiblePairs H X 0 : ℕ) := by
        exact_mod_cast hiNat
      apply NNReal.eq
      rw [NNReal.coe_sub hthreeNN]
      norm_cast
    rw [hcast]
    push_cast
    apply (le_tsub_iff_right hiNN).2
    calc
      (i : ℝ≥0) * rho + 3 * (i : ℝ≥0) =
          (i : ℝ≥0) * (3 + rho) := by push_cast; ring
      _ ≤ (outerSharpEligiblePairs H X 0 : ℕ) := by
        simpa only [perturbedOuterLowerSlope, perturbedOuterLowerR0] using hpos
  apply NNReal.eq
  unfold affineSurvivalEnvelope
  rw [NNReal.coe_sub hpos]
  unfold perturbedOuterLowerSlope perturbedOuterLowerR0
  rw [NNReal.coe_sub hrhoTerm, heligible]
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast]
  rw [Nat.cast_sub hiNat]
  push_cast
  ring

end

end Erdos207
