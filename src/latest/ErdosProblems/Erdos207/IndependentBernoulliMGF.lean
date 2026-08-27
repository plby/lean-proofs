/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteKernelConcentration

/-! # Centered exponential moments for nonidentical independent Bernoulli bits -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem bernoulli_centered_exp_le (p theta : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (htheta : |theta| ≤ 1) :
    (1 - p) * Real.exp (-theta * p) + p * Real.exp (theta * (1 - p)) ≤
      Real.exp (theta ^ 2 * p) := by
  have hpabs : |p| ≤ 1 := by simpa only [abs_of_nonneg hp0] using hp1
  have hqabs : |1 - p| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have harg1 : -theta * p ≤ 1 := by
    apply (le_abs_self _).trans
    rw [abs_mul, abs_neg]
    exact (mul_le_mul htheta hpabs (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have harg2 : theta * (1 - p) ≤ 1 := by
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact (mul_le_mul htheta hqabs (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have h1 := mul_le_mul_of_nonneg_left
    (FiniteLaw.exp_le_one_add_self_add_sq_of_le_one harg1) (show 0 ≤ 1 - p by linarith)
  have h2 := mul_le_mul_of_nonneg_left
    (FiniteLaw.exp_le_one_add_self_add_sq_of_le_one harg2) hp0
  calc
    _ ≤ (1 - p) * (1 + -theta * p + (-theta * p) ^ 2) +
        p * (1 + theta * (1 - p) + (theta * (1 - p)) ^ 2) := add_le_add h1 h2
    _ = 1 + theta ^ 2 * p - theta ^ 2 * p ^ 2 := by ring
    _ ≤ 1 + theta ^ 2 * p := sub_le_self _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (theta ^ 2 * p)

theorem FiniteLaw.independentBits_expectationReal_prod
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (f : I → Bool → ℝ) :
    (independentBits p hp).expectationReal (fun ω ↦ ∏ i, f i (ω i)) =
      ∏ i, ∑ b : Bool, (bernoulliBitMass (p i) b : ℝ) * f i b := by
  unfold expectationReal
  simp only [independentBits_mass, NNReal.coe_prod]
  simp_rw [← prod_mul_distrib]
  exact (Fintype.prod_sum
    (fun i (b : Bool) ↦ (bernoulliBitMass (p i) b : ℝ) * f i b)).symm

theorem FiniteLaw.independentBits_centered_exp_mgf
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (theta : I → ℝ) (htheta : ∀ i, |theta i| ≤ 1) :
    (independentBits p hp).expectationReal
      (fun ω ↦ Real.exp (∑ i, theta i * ((if ω i then 1 else 0) - (p i : ℝ)))) ≤
      Real.exp (∑ i, (theta i) ^ 2 * (p i : ℝ)) := by
  simp_rw [Real.exp_sum]
  rw [independentBits_expectationReal_prod p hp
    (fun i b ↦ Real.exp (theta i * ((if b then 1 else 0) - (p i : ℝ))))]
  apply prod_le_prod
  · intro i _hi
    exact sum_nonneg (fun _ _ ↦ mul_nonneg (NNReal.coe_nonneg _) (Real.exp_pos _).le)
  · intro i _hi
    have hpReal : (p i : ℝ) ≤ 1 := by exact_mod_cast hp i
    have hbit := bernoulli_centered_exp_le (p i) (theta i) (NNReal.coe_nonneg _) hpReal (htheta i)
    simpa only [Fintype.sum_bool, bernoulliBitMass, Bool.false_eq_true, ↓reduceIte,
      NNReal.coe_sub (hp i), NNReal.coe_one, zero_sub, mul_neg, neg_mul, mul_one,
      add_comm] using hbit

end

end Erdos207
