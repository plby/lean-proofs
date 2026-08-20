/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperWeightedExceptionalSumFinal
import ErdosProblems.Erdos446.UpperDoubleExponentialSum
import ErdosProblems.Erdos446.UpperNegativeDepthSum
import ErdosProblems.Erdos446.UpperCentralDepthSum
import ErdosProblems.Erdos446.UpperExceptionalLayerSum

/-!
# Erdős Problem 446: numerical summation of the closed weighted layers

This file sums the two estimates from `UpperWeightedExceptionalSumFinal`
over the canonical integral layer parameter.  The result is the signed
central-depth factor used in Ford's final `k`-sum.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable def fordWeightedHighLayerNumerical (k v : ℕ) : ℝ :=
  ∑ γ ∈ (Finset.range (k + 1)).filter (fun γ ↦ v + γ + 5 ≤ k),
    ((k - v : ℕ) : ℝ) /
      ((2 : ℝ) ^ γ * (2 : ℝ) ^ (2 ^ (k - v - γ)))

noncomputable def fordWeightedLowLayerNumerical (k v : ℕ) : ℝ :=
  ∑ γ ∈ (Finset.range (k + 1)).filter (fun γ ↦ k < v + γ + 5),
    ((γ + 1 : ℕ) : ℝ) * ((γ + 5 + v - k : ℕ) : ℝ) ^ 2 /
      (2 : ℝ) ^ γ

private theorem index_le_two_pow (j : ℕ) : j ≤ 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ j := one_le_pow₀ (by omega)
      omega

private theorem quadratic_model_conversion (b : ℕ) :
    (1 + (b : ℝ) ^ 2) / (2 : ℝ) ^ b ≤
      2 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hden : (0 : ℝ) < (2 : ℝ) ^ b + 1 := by positivity
  have hratio : (2 : ℝ) ^ b + 1 ≤ 2 * (2 : ℝ) ^ b := by
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
    linarith
  apply (div_le_div_iff₀ hpow hden).2
  calc
    (1 + (b : ℝ) ^ 2) * ((2 : ℝ) ^ b + 1) ≤
        (1 + (b : ℝ) ^ 2) * (2 * (2 : ℝ) ^ b) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (2 * (1 + (b : ℝ) ^ 2)) * (2 : ℝ) ^ b := by ring

/-- The double-exponential part of the layer sum has the sharp signed
central-depth decay. -/
theorem fordWeightedHighLayerNumerical_le
    {k v : ℕ} (hvk : v ≤ k) :
    fordWeightedHighLayerNumerical k v ≤
      2 * (1 + ((k - v : ℕ) : ℝ) ^ 2) /
        ((2 : ℝ) ^ (k - v) + 1) := by
  let b := k - v
  let I := (Finset.range (k + 1)).filter (fun γ ↦ v + γ + 5 ≤ k)
  have hterm : ∀ γ ∈ I,
      (b : ℝ) / ((2 : ℝ) ^ γ * (2 : ℝ) ^ (2 ^ (b - γ))) ≤
        (b : ℝ) / (2 : ℝ) ^ b := by
    intro γ hγ
    have hdata := Finset.mem_filter.mp hγ
    have hγb : γ < b := by dsimp [b]; omega
    have hexp : b ≤ γ + 2 ^ (b - γ) := by
      have hsplit : b = γ + (b - γ) := by omega
      calc
        b = γ + (b - γ) := hsplit
        _ ≤ γ + 2 ^ (b - γ) :=
          Nat.add_le_add_left (index_le_two_pow (b - γ)) γ
    have hden : (2 : ℝ) ^ b ≤
        (2 : ℝ) ^ γ * (2 : ℝ) ^ (2 ^ (b - γ)) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num) hexp
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hcard : I.card ≤ b := by
    have hsub : I ⊆ Finset.range b := by
      intro γ hγ
      rw [Finset.mem_range]
      have hdata := Finset.mem_filter.mp hγ
      dsimp [b]
      omega
    simpa using Finset.card_le_card hsub
  calc
    fordWeightedHighLayerNumerical k v =
        ∑ γ ∈ I,
          (b : ℝ) / ((2 : ℝ) ^ γ * (2 : ℝ) ^ (2 ^ (b - γ))) := by
      rfl
    _ ≤ I.card • ((b : ℝ) / (2 : ℝ) ^ b) :=
      Finset.sum_le_card_nsmul I _ _ hterm
    _ = (I.card : ℝ) * ((b : ℝ) / (2 : ℝ) ^ b) := by
      rw [nsmul_eq_mul]
    _ ≤ (b : ℝ) * ((b : ℝ) / (2 : ℝ) ^ b) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = (b : ℝ) ^ 2 / (2 : ℝ) ^ b := by ring
    _ ≤ (1 + (b : ℝ) ^ 2) / (2 : ℝ) ^ b := by
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ 2 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) :=
      quadratic_model_conversion b

private theorem fordWeightedLowLayerNumerical_le_large
    {k v : ℕ} (hvk : v ≤ k) (hb : 6 ≤ k - v) :
    fordWeightedLowLayerNumerical k v ≤
      ford33aPolynomialTail (k - v) (k + 1 - (k - v - 5)) := by
  let b := k - v
  let a := b - 5
  let I := (Finset.range (k + 1)).filter (fun γ ↦ k < v + γ + 5)
  let f : ℕ → ℝ := fun γ ↦
    ((γ + 1 : ℕ) : ℝ) * ((γ + 5 + v - k : ℕ) : ℝ) ^ 2 /
      (2 : ℝ) ^ γ
  have hkb : k = v + b := by dsimp [b]; omega
  have hsub : I ⊆ Finset.Ico a (k + 1) := by
    intro γ hγ
    have hd := Finset.mem_filter.mp hγ
    rw [Finset.mem_Ico]
    constructor
    · dsimp [a]
      rw [hkb] at hd
      omega
    · exact Finset.mem_range.mp hd.1
  have henlarge : (∑ γ ∈ I, f γ) ≤
      ∑ γ ∈ Finset.Ico a (k + 1), f γ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i hi hin ↦ by dsimp [f]; positivity)
  calc
    fordWeightedLowLayerNumerical k v = ∑ γ ∈ I, f γ := by rfl
    _ ≤ ∑ γ ∈ Finset.Ico a (k + 1), f γ := henlarge
    _ = ∑ w ∈ Finset.range (k + 1 - a), f (a + w) := by
      rw [Finset.sum_Ico_eq_sum_range]
    _ ≤ ∑ w ∈ Finset.range (k + 1 - a),
        ((w + 1 : ℕ) : ℝ) ^ 2 * ((b + w - 3 : ℕ) : ℝ) /
          (2 : ℝ) ^ (b - 5 + w) := by
      apply Finset.sum_le_sum
      intro w hw
      have ha : a = b - 5 := rfl
      have hdelta : a + w + 5 + v - k = w := by
        dsimp [a, b]
        omega
      have hfirst : a + w + 1 ≤ b + w - 3 := by
        dsimp [a]
        omega
      dsimp [f]
      rw [hdelta, ha]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hfirstR : ((a + w + 1 : ℕ) : ℝ) ≤
          ((b + w - 3 : ℕ) : ℝ) := by exact_mod_cast hfirst
      have hwR : (w : ℝ) ≤ ((w + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_succ w)
      have hsq : (w : ℝ) ^ 2 ≤ ((w + 1 : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hwR 2
      simpa only [mul_comm] using
        mul_le_mul hfirstR hsq (sq_nonneg _) (by positivity)
    _ = ford33aPolynomialTail b (k + 1 - a) := by
      rw [ford33aPolynomialTail, if_pos (by simpa only [b] using hb)]

private theorem fordWeightedLowLayerNumerical_le_small
    {k v : ℕ} (hvk : v ≤ k) (hb : k - v < 6) :
    fordWeightedLowLayerNumerical k v ≤
      ford33aPolynomialTail (k - v) (k + 1) := by
  let b := k - v
  let I := (Finset.range (k + 1)).filter (fun γ ↦ k < v + γ + 5)
  let f : ℕ → ℝ := fun γ ↦
    ((γ + 1 : ℕ) : ℝ) * ((γ + 5 + v - k : ℕ) : ℝ) ^ 2 /
      (2 : ℝ) ^ γ
  have henlarge : (∑ γ ∈ I, f γ) ≤
      ∑ γ ∈ Finset.range (k + 1), f γ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i hi hin ↦ by dsimp [f]; positivity)
  calc
    fordWeightedLowLayerNumerical k v = ∑ γ ∈ I, f γ := by rfl
    _ ≤ ∑ γ ∈ Finset.range (k + 1), f γ := henlarge
    _ ≤ ∑ γ ∈ Finset.range (k + 1),
        ((γ + 6 - b : ℕ) : ℝ) ^ 2 * ((γ + 2 : ℕ) : ℝ) /
          (2 : ℝ) ^ γ := by
      apply Finset.sum_le_sum
      intro γ hγ
      have hdelta : γ + 5 + v - k ≤ γ + 6 - b := by
        dsimp [b]
        omega
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hdeltaR : ((γ + 5 + v - k : ℕ) : ℝ) ≤
          ((γ + 6 - b : ℕ) : ℝ) := by exact_mod_cast hdelta
      have hsq : ((γ + 5 + v - k : ℕ) : ℝ) ^ 2 ≤
          ((γ + 6 - b : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hdeltaR 2
      have hfirstR : ((γ + 1 : ℕ) : ℝ) ≤
          ((γ + 2 : ℕ) : ℝ) := by exact_mod_cast (show γ + 1 ≤ γ + 2 by omega)
      simpa only [mul_comm] using
        mul_le_mul hfirstR hsq (sq_nonneg _) (by positivity)
    _ = ford33aPolynomialTail b (k + 1) := by
      rw [ford33aPolynomialTail, if_neg (by dsimp [b]; omega)]

/-- The polynomial part of the layer sum above the center. -/
theorem fordWeightedLowLayerNumerical_le_of_le
    {k v : ℕ} (hvk : v ≤ k) :
    fordWeightedLowLayerNumerical k v ≤
      8192 * (1 + ((k - v : ℕ) : ℝ) ^ 2) /
        ((2 : ℝ) ^ (k - v) + 1) := by
  by_cases hb : 6 ≤ k - v
  · exact (fordWeightedLowLayerNumerical_le_large hvk hb).trans
      (ford33aPolynomialTail_le (k - v) (k + 1 - (k - v - 5)))
  · have hb' : k - v < 6 := by omega
    exact (fordWeightedLowLayerNumerical_le_small hvk hb').trans
      (ford33aPolynomialTail_le (k - v) (k + 1))

/-- Below the center the low-depth sum is the negative-depth tail. -/
theorem fordWeightedLowLayerNumerical_le_of_lt
    {k v : ℕ} (hkv : k < v) :
    fordWeightedLowLayerNumerical k v ≤
      8192 * (1 + ((v - k : ℕ) : ℝ) ^ 2) := by
  let d := v - k
  let I := (Finset.range (k + 1)).filter (fun γ ↦ k < v + γ + 5)
  let f : ℕ → ℝ := fun γ ↦
    ((γ + 1 : ℕ) : ℝ) * ((γ + 5 + v - k : ℕ) : ℝ) ^ 2 /
      (2 : ℝ) ^ γ
  have hIfull : I = Finset.range (k + 1) := by
    apply Finset.filter_eq_self.mpr
    intro γ hγ
    omega
  calc
    fordWeightedLowLayerNumerical k v = ∑ γ ∈ I, f γ := by rfl
    _ = ∑ γ ∈ Finset.range (k + 1), f γ := by rw [hIfull]
    _ ≤ ∑ γ ∈ Finset.range (k + 1),
        ((γ + 6 + d : ℕ) : ℝ) ^ 2 * ((γ + 2 : ℕ) : ℝ) /
          (2 : ℝ) ^ γ := by
      apply Finset.sum_le_sum
      intro γ hγ
      have hdelta : γ + 5 + v - k ≤ γ + 6 + d := by
        dsimp [d]
        omega
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hdeltaR : ((γ + 5 + v - k : ℕ) : ℝ) ≤
          ((γ + 6 + d : ℕ) : ℝ) := by exact_mod_cast hdelta
      have hsq : ((γ + 5 + v - k : ℕ) : ℝ) ^ 2 ≤
          ((γ + 6 + d : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hdeltaR 2
      have hfirstR : ((γ + 1 : ℕ) : ℝ) ≤
          ((γ + 2 : ℕ) : ℝ) := by exact_mod_cast (show γ + 1 ≤ γ + 2 by omega)
      simpa only [mul_comm] using
        mul_le_mul hfirstR hsq (sq_nonneg _) (by positivity)
    _ = ford33aNegativeDepthTail d (k + 1) := by
      rw [ford33aNegativeDepthTail]
    _ ≤ 8192 * (1 + (d : ℝ) ^ 2) :=
      ford33aNegativeDepthTail_le d (k + 1)

/-- The reciprocal-factorial mass of all canonical weighted layers after
the geometric envelope factor `2^(k+1)` has been pulled out. -/
noncomputable def fordWeightedLayerReciprocalSum (k v : ℕ) : ℝ :=
  ∑ γ ∈ Finset.range (k + 1),
    reciprocalFactorialMassOver (fordWeightedOccupancies k v γ) /
      (2 : ℝ) ^ γ

/-- One absolute constant for both sides of the signed central depth. -/
noncomputable def fordWeightedLayerMassConstant : ℝ :=
  16384 * (fordWeightedHighMassConstant + fordWeightedLowMassConstant)

theorem fordWeightedLayerMassConstant_nonneg :
    0 ≤ fordWeightedLayerMassConstant := by
  rw [fordWeightedLayerMassConstant]
  exact mul_nonneg (by norm_num)
    (add_nonneg fordWeightedHighMassConstant_nonneg
      fordWeightedLowMassConstant_nonneg)

private theorem fordWeightedLayerReciprocalSum_le_numerical
    {k v : ℕ} (hv : 0 < v) (hkv : k ≤ 10 * v) :
    fordWeightedLayerReciprocalSum k v ≤
      fordWeightedHighMassConstant *
          ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) *
            fordWeightedHighLayerNumerical k v +
        fordWeightedLowMassConstant *
          ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) *
            fordWeightedLowLayerNumerical k v := by
  let S := Finset.range (k + 1)
  let P : ℕ → Prop := fun γ ↦ v + γ + 5 ≤ k
  let F : ℕ → ℝ := fun γ ↦
    reciprocalFactorialMassOver (fordWeightedOccupancies k v γ) /
      (2 : ℝ) ^ γ
  have hsplit := Finset.sum_filter_add_sum_filter_not S P F
  have hhigh : (∑ γ ∈ S with P γ, F γ) ≤
      fordWeightedHighMassConstant *
        ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) *
          fordWeightedHighLayerNumerical k v := by
    calc
      (∑ γ ∈ S with P γ, F γ) ≤
          ∑ γ ∈ S with P γ,
            fordWeightedHighMassConstant *
              ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) *
                (((k - v : ℕ) : ℝ) /
                  ((2 : ℝ) ^ γ * (2 : ℝ) ^ (2 ^ (k - v - γ)))) := by
        apply Finset.sum_le_sum
        intro γ hγ
        have hp : P γ := (Finset.mem_filter.mp hγ).2
        have hm := reciprocalFactorialMassOver_fordWeightedOccupancies_le_high
          hv hkv (by simpa only [P] using hp)
        dsimp [F]
        calc
          reciprocalFactorialMassOver (fordWeightedOccupancies k v γ) /
                (2 : ℝ) ^ γ ≤
              (fordWeightedHighMassConstant * ((k - v : ℕ) : ℝ) /
                (2 : ℝ) ^ (2 ^ (k - v - γ)) *
                  ((v : ℝ) ^ k / ((k + 1).factorial : ℝ))) /
                    (2 : ℝ) ^ γ :=
            div_le_div_of_nonneg_right hm (by positivity)
          _ = _ := by ring
      _ = fordWeightedHighMassConstant *
          ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) *
            fordWeightedHighLayerNumerical k v := by
        rw [fordWeightedHighLayerNumerical, Finset.mul_sum]
  have hlow : (∑ γ ∈ S with ¬P γ, F γ) ≤
      fordWeightedLowMassConstant *
        ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) *
          fordWeightedLowLayerNumerical k v := by
    calc
      (∑ γ ∈ S with ¬P γ, F γ) ≤
          ∑ γ ∈ S with ¬P γ,
            fordWeightedLowMassConstant *
              ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) *
                (((γ + 1 : ℕ) : ℝ) *
                  ((γ + 5 + v - k : ℕ) : ℝ) ^ 2 /
                    (2 : ℝ) ^ γ) := by
        apply Finset.sum_le_sum
        intro γ hγ
        have hp : ¬P γ := (Finset.mem_filter.mp hγ).2
        have hm := reciprocalFactorialMassOver_fordWeightedOccupancies_le_low
          (k := k) (v := v) (γ := γ) hv hkv (by dsimp [P] at hp; omega)
        dsimp [F]
        calc
          reciprocalFactorialMassOver (fordWeightedOccupancies k v γ) /
                (2 : ℝ) ^ γ ≤
              (fordWeightedLowMassConstant * ((γ + 1 : ℕ) : ℝ) *
                ((γ + 5 + v - k : ℕ) : ℝ) ^ 2 *
                  ((v : ℝ) ^ k / ((k + 1).factorial : ℝ))) /
                    (2 : ℝ) ^ γ :=
            div_le_div_of_nonneg_right hm (by positivity)
          _ = _ := by ring
      _ = fordWeightedLowMassConstant *
          ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) *
            fordWeightedLowLayerNumerical k v := by
        rw [fordWeightedLowLayerNumerical, Finset.mul_sum]
        simp only [S, P, not_le]
  calc
    fordWeightedLayerReciprocalSum k v = ∑ γ ∈ S, F γ := by rfl
    _ = (∑ γ ∈ S with P γ, F γ) +
        (∑ γ ∈ S with ¬P γ, F γ) := hsplit.symm
    _ ≤ _ := add_le_add hhigh hlow

/-- Fully summed canonical weighted-layer estimate in Ford's signed central
form. -/
theorem fordWeightedLayerReciprocalSum_le_central
    {k v : ℕ} (hv : 0 < v) (hkv : k ≤ 10 * v) :
    fordWeightedLayerReciprocalSum k v ≤
      fordWeightedLayerMassConstant *
        fordCentralDepthTerm (v : ℝ) v k := by
  have hraw := fordWeightedLayerReciprocalSum_le_numerical hv hkv
  let B := (v : ℝ) ^ k / ((k + 1).factorial : ℝ)
  by_cases hvk : v ≤ k
  · have hH := fordWeightedHighLayerNumerical_le hvk
    have hL := fordWeightedLowLayerNumerical_le_of_le hvk
    have hmodel : 0 ≤
        (1 + ((k - v : ℕ) : ℝ) ^ 2) /
          ((2 : ℝ) ^ (k - v) + 1) := by positivity
    apply hraw.trans
    rw [fordWeightedLayerMassConstant, fordCentralDepthTerm,
      fordPoissonFactor, signedTwoPower_eq_pow_of_le hvk,
      Nat.dist_eq_sub_of_le hvk]
    calc
      fordWeightedHighMassConstant * B * fordWeightedHighLayerNumerical k v +
          fordWeightedLowMassConstant * B * fordWeightedLowLayerNumerical k v ≤
        fordWeightedHighMassConstant * B * (2 *
            (1 + ((k - v : ℕ) : ℝ) ^ 2) /
              ((2 : ℝ) ^ (k - v) + 1)) +
          fordWeightedLowMassConstant * B * (8192 *
            (1 + ((k - v : ℕ) : ℝ) ^ 2) /
              ((2 : ℝ) ^ (k - v) + 1)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hH (mul_nonneg
            fordWeightedHighMassConstant_nonneg (by dsimp [B]; positivity)))
          (mul_le_mul_of_nonneg_left hL (mul_nonneg
            fordWeightedLowMassConstant_nonneg (by dsimp [B]; positivity)))
      _ ≤ 16384 * (fordWeightedHighMassConstant + fordWeightedLowMassConstant) *
          (B * (1 + ((k - v : ℕ) : ℝ) ^ 2) /
            ((2 : ℝ) ^ (k - v) + 1)) := by
        have hcoef : 2 * fordWeightedHighMassConstant +
            8192 * fordWeightedLowMassConstant ≤
              16384 * (fordWeightedHighMassConstant +
                fordWeightedLowMassConstant) := by
          nlinarith [fordWeightedHighMassConstant_nonneg,
            fordWeightedLowMassConstant_nonneg]
        have hBQ : 0 ≤ B * ((1 + ((k - v : ℕ) : ℝ) ^ 2) /
            ((2 : ℝ) ^ (k - v) + 1)) := by
          exact mul_nonneg (by dsimp [B]; positivity) hmodel
        calc
          fordWeightedHighMassConstant * B * (2 *
                (1 + ((k - v : ℕ) : ℝ) ^ 2) /
                  ((2 : ℝ) ^ (k - v) + 1)) +
              fordWeightedLowMassConstant * B * (8192 *
                (1 + ((k - v : ℕ) : ℝ) ^ 2) /
                  ((2 : ℝ) ^ (k - v) + 1)) =
              (2 * fordWeightedHighMassConstant +
                8192 * fordWeightedLowMassConstant) *
                  (B * ((1 + ((k - v : ℕ) : ℝ) ^ 2) /
                    ((2 : ℝ) ^ (k - v) + 1))) := by ring
          _ ≤ 16384 * (fordWeightedHighMassConstant +
                fordWeightedLowMassConstant) *
                  (B * ((1 + ((k - v : ℕ) : ℝ) ^ 2) /
                    ((2 : ℝ) ^ (k - v) + 1))) :=
            mul_le_mul_of_nonneg_right hcoef hBQ
          _ = 16384 * (fordWeightedHighMassConstant +
                fordWeightedLowMassConstant) *
                  (B * (1 + ((k - v : ℕ) : ℝ) ^ 2) /
                    ((2 : ℝ) ^ (k - v) + 1)) := by ring
      _ = 16384 * (fordWeightedHighMassConstant + fordWeightedLowMassConstant) *
          ((v : ℝ) ^ k / ((k + 1).factorial : ℝ) *
            (1 + ((k - v : ℕ) : ℝ) ^ 2) /
              ((2 : ℝ) ^ (k - v) + 1)) := by rfl
  · have hlt : k < v := Nat.lt_of_not_ge hvk
    have hH0 : fordWeightedHighLayerNumerical k v = 0 := by
      rw [fordWeightedHighLayerNumerical]
      apply Finset.sum_eq_zero
      intro γ hγ
      have hp := (Finset.mem_filter.mp hγ).2
      omega
    have hL := fordWeightedLowLayerNumerical_le_of_lt hlt
    have hpowLe : signedTwoPower k v + 1 ≤ 2 := by
      rw [signedTwoPower_eq_inv_pow_of_le hlt.le]
      have hi : ((2 : ℝ) ^ (v - k))⁻¹ ≤ 1 := by
        exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
      linarith
    have hdenPos : 0 < signedTwoPower k v + 1 := by
      linarith [signedTwoPower_pos k v]
    apply hraw.trans
    rw [hH0, mul_zero, zero_add, fordWeightedLayerMassConstant,
      fordCentralDepthTerm, fordPoissonFactor, Nat.dist_comm v k,
      Nat.dist_eq_sub_of_le hlt.le]
    have hmodel : (1 + ((v - k : ℕ) : ℝ) ^ 2) ≤
        2 * ((1 + ((v - k : ℕ) : ℝ) ^ 2) /
          (signedTwoPower k v + 1)) := by
      calc
        (1 + ((v - k : ℕ) : ℝ) ^ 2) ≤
            (2 * (1 + ((v - k : ℕ) : ℝ) ^ 2)) /
              (signedTwoPower k v + 1) := by
          apply (le_div_iff₀ hdenPos).2
          have hA : 0 ≤ 1 + ((v - k : ℕ) : ℝ) ^ 2 := by positivity
          nlinarith
        _ = 2 * ((1 + ((v - k : ℕ) : ℝ) ^ 2) /
            (signedTwoPower k v + 1)) := by ring
    calc
      fordWeightedLowMassConstant * B * fordWeightedLowLayerNumerical k v ≤
          fordWeightedLowMassConstant * B *
            (8192 * (1 + ((v - k : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hL
          (mul_nonneg fordWeightedLowMassConstant_nonneg
            (by dsimp [B]; positivity))
      _ ≤ fordWeightedLowMassConstant * B *
          (16384 * ((1 + ((v - k : ℕ) : ℝ) ^ 2) /
            (signedTwoPower k v + 1))) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg fordWeightedLowMassConstant_nonneg
            (by dsimp [B]; positivity))
        calc
          8192 * (1 + ((v - k : ℕ) : ℝ) ^ 2) ≤
              8192 * (2 * ((1 + ((v - k : ℕ) : ℝ) ^ 2) /
                (signedTwoPower k v + 1))) :=
            mul_le_mul_of_nonneg_left hmodel (by norm_num)
          _ = 16384 * ((1 + ((v - k : ℕ) : ℝ) ^ 2) /
                (signedTwoPower k v + 1)) := by ring
      _ ≤ 16384 * (fordWeightedHighMassConstant + fordWeightedLowMassConstant) *
          (B * (1 + ((v - k : ℕ) : ℝ) ^ 2) /
            (signedTwoPower k v + 1)) := by
        have hcoef : fordWeightedLowMassConstant ≤
            fordWeightedHighMassConstant + fordWeightedLowMassConstant := by
          linarith [fordWeightedHighMassConstant_nonneg]
        have hBQ : 0 ≤ B * ((1 + ((v - k : ℕ) : ℝ) ^ 2) /
            (signedTwoPower k v + 1)) := by positivity
        calc
          fordWeightedLowMassConstant * B *
              (16384 * ((1 + ((v - k : ℕ) : ℝ) ^ 2) /
                (signedTwoPower k v + 1))) =
            16384 * fordWeightedLowMassConstant *
              (B * ((1 + ((v - k : ℕ) : ℝ) ^ 2) /
                (signedTwoPower k v + 1))) := by ring
          _ ≤ 16384 * (fordWeightedHighMassConstant +
                fordWeightedLowMassConstant) *
              (B * ((1 + ((v - k : ℕ) : ℝ) ^ 2) /
                (signedTwoPower k v + 1))) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hBQ
          _ = 16384 * (fordWeightedHighMassConstant +
                fordWeightedLowMassConstant) *
              (B * (1 + ((v - k : ℕ) : ℝ) ^ 2) /
                (signedTwoPower k v + 1)) := by ring

/-- Concrete fixed-`k` arithmetic consequence when the finite block-offset
condition holds.  This is useful independently of the later residual-pool
argument and records exactly where the older uniform Mertens transfer is
valid. -/
theorem blockClusterMassOver_compositions_le_central_of_offset
    {M k v : ℕ} {C : ℝ} (hv : 0 < v) (hkv : k ≤ 10 * v)
    (hC : 0 ≤ C) (hM : k + blockLayerSlack k + 1 ≤ 2 ^ M)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val)) :
    blockClusterMassOver M (compositionsOf v k) ≤
      sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
          (fordWeightedLayerMassConstant *
            fordCentralDepthTerm (v : ℝ) v k) := by
  have hraw := blockClusterMassOver_compositions_le_fordWeightedMassSum
    hC hM hmass
    (fun γ ↦ reciprocalFactorialMassOver
      (fordWeightedOccupancies k v γ))
    (fun γ hγ ↦ le_rfl)
  apply hraw.trans
  have hsum := fordWeightedLayerReciprocalSum_le_central hv hkv
  exact mul_le_mul_of_nonneg_left hsum (by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (sharpBlockLayerScale_pos M).le (by positivity)) (by positivity))
        (Real.exp_pos _).le)

end Erdos446
