/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpRecursiveBarrier
import ErdosProblems.Erdos207.CubicSurvivalCancellation

/-!
# Quadratic barriers for the triangle-removal trajectory

If `R` is the remaining pair budget, the available degree of a live pair is
quadratic in `R`.  Separate affine pair envelopes with slightly different
slopes provide the sub- and super-solutions needed to absorb rounding and
martingale buffers.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

/-- A real quadratic barrier built from a positive affine pair envelope. -/
def quadraticPairBarrier
    (N coefficient R0 slope : ℝ≥0) (i : ℕ) : ℝ :=
  (coefficient * affineSurvivalEnvelope R0 slope i ^ 2 * N⁻¹ ^ 3 : ℝ≥0)

lemma quadraticPairBarrier_nonneg
    (N coefficient R0 slope : ℝ≥0) (i : ℕ) :
    0 ≤ quadraticPairBarrier N coefficient R0 slope i := by
  unfold quadraticPairBarrier
  positivity

/-- Exact one-step decrement of the quadratic barrier before the affine
envelope reaches zero. -/
lemma quadraticPairBarrier_sub_succ
    {N coefficient R0 slope : ℝ≥0} {fuel i : ℕ}
    (hpos : (fuel : ℝ≥0) * slope < R0) (hi : i < fuel) :
    quadraticPairBarrier N coefficient R0 slope i -
        quadraticPairBarrier N coefficient R0 slope (i + 1) =
      (coefficient * slope *
          (2 * affineSurvivalEnvelope R0 slope i - slope) * N⁻¹ ^ 3 :
        ℝ≥0) := by
  let Ri := affineSurvivalEnvelope R0 slope i
  let Rnext := affineSurvivalEnvelope R0 slope (i + 1)
  have hanti : Rnext ≤ Ri :=
    affineSurvivalEnvelope_antitone R0 slope (Nat.le_succ i)
  have hdec : Ri - Rnext = slope := by
    exact affineSurvivalEnvelope_sub_succ (le_of_lt hpos) hi
  have hstep : slope ≤ Ri := by
    rw [← hdec]
    exact tsub_le_self
  have htwo : slope ≤ 2 * Ri := hstep.trans (by
    simpa only [two_mul] using (le_add_self : Ri ≤ Ri + Ri))
  have htwo' : slope ≤ 2 * affineSurvivalEnvelope R0 slope i := by
    simpa only [Ri] using htwo
  simp only [quadraticPairBarrier, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_inv]
  rw [NNReal.coe_sub htwo']
  have hdecR :
      (affineSurvivalEnvelope R0 slope i : ℝ) -
          (affineSurvivalEnvelope R0 slope (i + 1) : ℝ) =
        (slope : ℝ) := by
    rw [← NNReal.coe_sub hanti]
    exact_mod_cast hdec
  rw [show (affineSurvivalEnvelope R0 slope (i + 1) : ℝ) =
      (affineSurvivalEnvelope R0 slope i : ℝ) - (slope : ℝ) by linarith]
  push_cast
  ring

/-- The quadratic barriers decrease while their affine envelopes remain
positive. -/
lemma quadraticPairBarrier_antitone_on
    {N coefficient R0 slope : ℝ≥0} {fuel i j : ℕ}
    (hpos : (fuel : ℝ≥0) * slope < R0) (hij : i ≤ j) (hj : j ≤ fuel) :
    quadraticPairBarrier N coefficient R0 slope j ≤
      quadraticPairBarrier N coefficient R0 slope i := by
  unfold quadraticPairBarrier
  exact_mod_cast mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left'
        (affineSurvivalEnvelope_antitone R0 slope hij) 2) zero_le)
    zero_le

/-- Natural ceilings and floors differ from a nonnegative real barrier by
less than one.  These two estimates are the only rounding losses used in
the rate comparison. -/
lemma nonnegativeNatCeil_lt_add_one {x : ℝ} (hx : 0 ≤ x) :
    (nonnegativeNatCeil x : ℝ) < x + 1 := by
  unfold nonnegativeNatCeil
  rw [max_eq_right hx]
  exact Nat.ceil_lt_add_one hx

lemma sub_one_lt_nonnegativeNatFloor {x : ℝ} (hx : 1 ≤ x) :
    x - 1 < (nonnegativeNatFloor x : ℝ) := by
  unfold nonnegativeNatFloor
  rw [max_eq_right (zero_le_one.trans hx)]
  have h := Nat.lt_floor_add_one x
  linarith

end

end Erdos207
