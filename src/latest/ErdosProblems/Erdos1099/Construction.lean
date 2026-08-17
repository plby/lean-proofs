/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Mathlib.Topology.Order.Basic

/-!
# The explicit integers used for Erdős Problem 1099

This file contains only the elementary arithmetic part of the construction.
For `k : ℕ`, put

* `triangular k = 1 + ⋯ + k`,
* `generator i = 2 ^ i + 1`,
* `voseNumber k = 2 ^ triangular k * ∏ i ∈ Icc 1 k, generator i`.

If `E ⊆ Icc 1 r` and `triangular r ≤ t ≤ triangular k`, the natural
number

`2 ^ (t - ∑ i ∈ E, i) * ∏ i ∈ E, (2 ^ i + 1)`

is visibly a divisor of `voseNumber k`.  Its logarithm is

`t * log 2 + ∑ i ∈ E, log (1 + (1 / 2) ^ i)`.

None of the divisibility arguments uses coprimality of the generators.
-/

open scoped BigOperators Topology
open Filter Finset

namespace Erdos1099

noncomputable section

/-- The triangular number `1 + ⋯ + k`.

The finite-sum definition is definitionally aligned with the index set used
by the generators. -/
def triangular (k : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 k, i

/-- The `i`-th elementary odd generator in the explicit construction. -/
def generator (i : ℕ) : ℕ := 2 ^ i + 1

/-- Product of the generators with indices from `1` through `k`. -/
def generatorProduct (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, generator i

/-- The explicit sequence of integers used in the construction. -/
def voseNumber (k : ℕ) : ℕ :=
  2 ^ triangular k * generatorProduct k

/-- Sum of the integer indices in a selected finite set. -/
def indexSum (E : Finset ℕ) : ℕ :=
  ∑ i ∈ E, i

/-- Product of the generators whose indices are selected by `E`. -/
def selectedProduct (E : Finset ℕ) : ℕ :=
  ∏ i ∈ E, generator i

/-- A selected divisor at integral logarithmic level `t`. -/
def selectedDivisor (t : ℕ) (E : Finset ℕ) : ℕ :=
  2 ^ (t - indexSum E) * selectedProduct E

/-- The small natural-log correction contributed by `generator i`. -/
def logDigit (i : ℕ) : ℝ :=
  Real.log (1 + (1 / 2 : ℝ) ^ i)

@[simp] lemma triangular_zero : triangular 0 = 0 := by
  simp [triangular]

lemma triangular_eq_sum_Icc (k : ℕ) :
    triangular k = ∑ i ∈ Finset.Icc 1 k, i := by
  rfl

lemma indexSum_le_triangular {E : Finset ℕ} {k : ℕ}
    (hE : E ⊆ Finset.Icc 1 k) : indexSum E ≤ triangular k := by
  rw [triangular_eq_sum_Icc, indexSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ ↦ Nat.zero_le _)

lemma generator_pos (i : ℕ) : 0 < generator i := by
  simp [generator]

lemma generator_ne_zero (i : ℕ) : generator i ≠ 0 :=
  Nat.ne_of_gt (generator_pos i)

lemma generatorProduct_pos (k : ℕ) : 0 < generatorProduct k := by
  simp [generatorProduct, generator_pos]

lemma generatorProduct_ne_zero (k : ℕ) : generatorProduct k ≠ 0 :=
  Nat.ne_of_gt (generatorProduct_pos k)

lemma voseNumber_pos (k : ℕ) : 0 < voseNumber k := by
  simp [voseNumber, generatorProduct, generator_pos]

lemma voseNumber_ne_zero (k : ℕ) : voseNumber k ≠ 0 :=
  Nat.ne_of_gt (voseNumber_pos k)

lemma pow_two_le_voseNumber (k : ℕ) :
    2 ^ triangular k ≤ voseNumber k := by
  rw [voseNumber]
  exact Nat.le_mul_of_pos_right (2 ^ triangular k) (generatorProduct_pos k)

lemma selectedProduct_dvd_generatorProduct {E : Finset ℕ} {k : ℕ}
    (hE : E ⊆ Finset.Icc 1 k) : selectedProduct E ∣ generatorProduct k := by
  classical
  rw [selectedProduct, generatorProduct]
  exact Finset.prod_dvd_prod_of_subset E (Finset.Icc 1 k) generator hE

/-- The selected number is an actual divisor of the explicit construction.
The more flexible hypotheses through `r` are the ones used by the logarithmic
shell construction. -/
lemma selectedDivisor_dvd {k r t : ℕ} {E : Finset ℕ}
    (hE : E ⊆ Finset.Icc 1 r) (hrk : r ≤ k)
    (hrt : triangular r ≤ t) (htk : t ≤ triangular k) :
    selectedDivisor t E ∣ voseNumber k := by
  have hEk : E ⊆ Finset.Icc 1 k :=
    hE.trans (Finset.Icc_subset_Icc_right hrk)
  have hsum_le_t : indexSum E ≤ t :=
    (indexSum_le_triangular hE).trans hrt
  have hpow : 2 ^ (t - indexSum E) ∣ 2 ^ triangular k := by
    exact pow_dvd_pow 2 (by omega)
  exact Nat.mul_dvd_mul hpow (selectedProduct_dvd_generatorProduct hEk)

lemma selectedDivisor_pos (t : ℕ) (E : Finset ℕ) :
    0 < selectedDivisor t E := by
  simp [selectedDivisor, selectedProduct, generator_pos]

lemma selectedDivisor_ne_zero (t : ℕ) (E : Finset ℕ) :
    selectedDivisor t E ≠ 0 :=
  Nat.ne_of_gt (selectedDivisor_pos t E)

lemma selectedProduct_pos (E : Finset ℕ) : 0 < selectedProduct E := by
  simp [selectedProduct, generator_pos]

lemma selectedProduct_ne_zero (E : Finset ℕ) : selectedProduct E ≠ 0 :=
  Nat.ne_of_gt (selectedProduct_pos E)

lemma generator_cast_eq (i : ℕ) :
    (generator i : ℝ) = (2 : ℝ) ^ i * (1 + (1 / 2 : ℝ) ^ i) := by
  rw [generator, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [mul_add, mul_one]
  have hcancel : (2 : ℝ) ^ i * (1 / 2 : ℝ) ^ i = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hcancel, add_comm]

lemma log_generator (i : ℕ) :
    Real.log (generator i : ℝ) = (i : ℝ) * Real.log 2 + logDigit i := by
  rw [generator_cast_eq, Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_pow]
  rfl

/-- Natural-log formula for every selected divisor. -/
lemma log_selectedDivisor {t : ℕ} {E : Finset ℕ}
    (hEt : indexSum E ≤ t) :
    Real.log (selectedDivisor t E : ℝ) =
      (t : ℝ) * Real.log 2 + ∑ i ∈ E, logDigit i := by
  classical
  rw [selectedDivisor, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (by positivity) (by exact_mod_cast selectedProduct_ne_zero E), Real.log_pow]
  rw [show Real.log (2 : ℝ) = Real.log 2 by rfl]
  rw [selectedProduct, Nat.cast_prod,
    Real.log_prod (fun i hi ↦ by exact_mod_cast generator_ne_zero i)]
  simp_rw [log_generator]
  push_cast
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  have hcast : (∑ i ∈ E, (i : ℝ)) = (indexSum E : ℝ) := by
    simp [indexSum]
  rw [hcast]
  rw [Nat.cast_sub hEt]
  ring

lemma triangular_mono : Monotone triangular := by
  intro a b hab
  rw [triangular_eq_sum_Icc, triangular_eq_sum_Icc]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right hab) (fun _ _ _ ↦ Nat.zero_le _)

lemma triangular_succ (k : ℕ) : triangular (k + 1) = triangular k + (k + 1) := by
  rw [triangular, triangular, Finset.sum_Icc_succ_top (by omega)]

lemma generatorProduct_succ (k : ℕ) :
    generatorProduct (k + 1) = generatorProduct k * generator (k + 1) := by
  rw [generatorProduct, generatorProduct, Finset.prod_Icc_succ_top (by omega)]

lemma voseNumber_succ (k : ℕ) :
    voseNumber (k + 1) =
      voseNumber k * (2 ^ (k + 1) * generator (k + 1)) := by
  rw [voseNumber, voseNumber, triangular_succ, generatorProduct_succ, pow_add]
  ac_rfl

lemma voseNumber_dvd_succ (k : ℕ) : voseNumber k ∣ voseNumber (k + 1) := by
  rw [voseNumber_succ]
  exact dvd_mul_right _ _

lemma voseNumber_dvd_of_le {j k : ℕ} (hjk : j ≤ k) :
    voseNumber j ∣ voseNumber k := by
  induction k with
  | zero => simp_all
  | succ k ih =>
      by_cases h : j ≤ k
      · exact (ih h).trans (voseNumber_dvd_succ k)
      · have : j = k + 1 := by omega
        subst j
        exact dvd_refl _

lemma triangular_ge_id (k : ℕ) : k ≤ triangular k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [triangular]
      apply Finset.single_le_sum (fun i _ ↦ Nat.zero_le i)
      simp

lemma triangular_tendsto_atTop : Tendsto triangular atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall triangular_ge_id) tendsto_id

lemma pow_two_triangular_tendsto_atTop :
    Tendsto (fun k : ℕ ↦ 2 ^ triangular k) atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
    triangular_tendsto_atTop

lemma voseNumber_tendsto_atTop : Tendsto voseNumber atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall pow_two_le_voseNumber)
    pow_two_triangular_tendsto_atTop

/-- Cofinality in the elementary form most convenient for the final theorem. -/
lemma exists_voseNumber_ge (B : ℕ) : ∃ k, B ≤ voseNumber k := by
  exact (tendsto_atTop.1 voseNumber_tendsto_atTop B).exists

end

end Erdos1099
