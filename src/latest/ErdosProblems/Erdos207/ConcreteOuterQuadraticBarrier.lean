/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RoundedOuterQuadraticBarrier

/-!
# Concrete rescaled quadratic barriers

The upper affine envelope is two thirds of the remaining all-pair budget and
has slope two.  The lower envelope is four thirds of the remaining eligible
pair budget and has slope four.  Thus both track the exact loss of three
pairs per selected triangle, while their quadratic coefficients normalize
to `17/4` and `15/4` respectively.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

def concreteOuterUpperCoefficient : ℝ≥0 := 153 / 16
def concreteOuterLowerCoefficient : ℝ≥0 := 135 / 64
def concreteOuterUpperSlope : ℝ≥0 := 2
def concreteOuterLowerSlope : ℝ≥0 := 4

def concreteOuterUpperR0 (V : Type*) [Fintype V] : ℝ≥0 :=
  (2 / 3) * (Nat.choose (Fintype.card V) 2 : ℕ)

def concreteOuterLowerR0
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) : ℝ≥0 :=
  (4 / 3) * (outerSharpEligiblePairs H X 0 : ℕ)

lemma concreteOuterUpperEnvelope_eq
    (V : Type*) [Fintype V] (i : ℕ)
    (hi : 3 * i ≤ Nat.choose (Fintype.card V) 2) :
    affineSurvivalEnvelope (concreteOuterUpperR0 V)
        concreteOuterUpperSlope i =
      (2 / 3 : ℝ≥0) * (outerSharpAllPairs V i : ℕ) := by
  apply NNReal.eq
  have hiNN : (3 : ℝ≥0) * (i : ℝ≥0) ≤
      (Nat.choose (Fintype.card V) 2 : ℕ) := by
    exact_mod_cast hi
  have hsub : (i : ℝ≥0) * concreteOuterUpperSlope ≤
      concreteOuterUpperR0 V := by
    rw [← NNReal.coe_le_coe]
    have hi' : (3 : ℝ) * i ≤ Nat.choose (Fintype.card V) 2 := by
      exact_mod_cast hi
    simp only [concreteOuterUpperSlope, concreteOuterUpperR0, NNReal.coe_mul,
      NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_ofNat]
    norm_num
    nlinarith
  simp only [affineSurvivalEnvelope, NNReal.coe_sub hsub]
  unfold concreteOuterUpperR0 concreteOuterUpperSlope outerSharpAllPairs
  push_cast
  rw [NNReal.coe_sub hiNN]
  norm_num
  ring

lemma concreteOuterLowerEnvelope_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (i : ℕ)
    (hi : 3 * i ≤ outerSharpEligiblePairs H X 0) :
    affineSurvivalEnvelope (concreteOuterLowerR0 H X)
        concreteOuterLowerSlope i =
      (4 / 3 : ℝ≥0) * (outerSharpEligiblePairs H X i : ℕ) := by
  have heligible : outerSharpEligiblePairs H X i =
      outerSharpEligiblePairs H X 0 - 3 * i := by
    unfold outerSharpEligiblePairs
    omega
  apply NNReal.eq
  have hiNN : (3 : ℝ≥0) * (i : ℝ≥0) ≤
      (outerSharpEligiblePairs H X 0 : ℕ) := by
    exact_mod_cast hi
  have hsub : (i : ℝ≥0) * concreteOuterLowerSlope ≤
      concreteOuterLowerR0 H X := by
    rw [← NNReal.coe_le_coe]
    have hi' : (3 : ℝ) * i ≤ outerSharpEligiblePairs H X 0 := by
      exact_mod_cast hi
    simp only [concreteOuterLowerSlope, concreteOuterLowerR0, NNReal.coe_mul,
      NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_ofNat]
    norm_num
    nlinarith
  simp only [affineSurvivalEnvelope, NNReal.coe_sub hsub]
  rw [heligible]
  unfold concreteOuterLowerR0 concreteOuterLowerSlope
  push_cast
  rw [NNReal.coe_sub hiNN]
  norm_num
  ring

/-- The concrete upper quadratic barrier is exactly `17/4` times the square
of the current all-pair budget, divided by the ambient cube. -/
lemma concreteOuterUpperBarrier_eq
    (V : Type*) [Fintype V] (N : ℝ≥0) (i : ℕ)
    (hi : 3 * i ≤ Nat.choose (Fintype.card V) 2) :
    quadraticPairBarrier N concreteOuterUpperCoefficient
        (concreteOuterUpperR0 V) concreteOuterUpperSlope i =
      (((17 / 4 : ℝ≥0) * (outerSharpAllPairs V i : ℕ) ^ 2 *
        N⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
  unfold quadraticPairBarrier
  rw [concreteOuterUpperEnvelope_eq V i hi]
  have hc : concreteOuterUpperCoefficient * (2 / 3 : ℝ≥0) ^ 2 =
      17 / 4 := by
    norm_num [concreteOuterUpperCoefficient]
  exact congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) (by
    calc
      concreteOuterUpperCoefficient *
            ((2 / 3 : ℝ≥0) * (outerSharpAllPairs V i : ℕ)) ^ 2 *
          N⁻¹ ^ 3 =
        (concreteOuterUpperCoefficient * (2 / 3 : ℝ≥0) ^ 2) *
          (outerSharpAllPairs V i : ℕ) ^ 2 * N⁻¹ ^ 3 := by ring
      _ = (17 / 4 : ℝ≥0) * (outerSharpAllPairs V i : ℕ) ^ 2 *
          N⁻¹ ^ 3 := by rw [hc])

/-- The concrete lower quadratic barrier is exactly `15/4` times the square
of the current eligible-pair budget, divided by the ambient cube. -/
lemma concreteOuterLowerBarrier_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (N : ℝ≥0) (i : ℕ)
    (hi : 3 * i ≤ outerSharpEligiblePairs H X 0) :
    quadraticPairBarrier N concreteOuterLowerCoefficient
        (concreteOuterLowerR0 H X) concreteOuterLowerSlope i =
      (((15 / 4 : ℝ≥0) * (outerSharpEligiblePairs H X i : ℕ) ^ 2 *
        N⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
  unfold quadraticPairBarrier
  rw [concreteOuterLowerEnvelope_eq H X i hi]
  have hc : concreteOuterLowerCoefficient * (4 / 3 : ℝ≥0) ^ 2 =
      15 / 4 := by
    norm_num [concreteOuterLowerCoefficient]
  exact congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) (by
    calc
      concreteOuterLowerCoefficient *
            ((4 / 3 : ℝ≥0) * (outerSharpEligiblePairs H X i : ℕ)) ^ 2 *
          N⁻¹ ^ 3 =
        (concreteOuterLowerCoefficient * (4 / 3 : ℝ≥0) ^ 2) *
          (outerSharpEligiblePairs H X i : ℕ) ^ 2 * N⁻¹ ^ 3 := by ring
      _ = (15 / 4 : ℝ≥0) * (outerSharpEligiblePairs H X i : ℕ) ^ 2 *
          N⁻¹ ^ 3 := by rw [hc])

end

end Erdos207
