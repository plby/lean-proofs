/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

/-!
# From logarithmically weighted counts to ordinary counts

This file contains an arithmetic-free form of the standard partial-summation
step in the prime number theorem.  A predicate on the natural numbers plays
the role of an arbitrary set of primes.
-/

namespace Erdos980.NaturalChebotarev

open Asymptotics Filter Finset MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The logarithmically weighted number of elements of `S` below `N`. -/
def logWeightedCount (S : ℕ → Prop) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, if S n then Real.log (n : ℝ) else 0

/-- The number of elements of `S` below `N`. -/
def predicateCount (S : ℕ → Prop) (N : ℕ) : ℕ :=
  ((range N).filter S).card

private def weightedIndicator (S : ℕ → Prop) (n : ℕ) : ℝ :=
  if S n then Real.log (n : ℝ) else 0

private def weightedCountLE (S : ℕ → Prop) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 0 N, weightedIndicator S n

private def countTwoLE (S : ℕ → Prop) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 0 N, if 2 ≤ n ∧ S n then 1 else 0

@[simp] private lemma weightedIndicator_zero (S : ℕ → Prop) :
    weightedIndicator S 0 = 0 := by
  simp [weightedIndicator]

@[simp] private lemma weightedIndicator_one (S : ℕ → Prop) :
    weightedIndicator S 1 = 0 := by
  simp [weightedIndicator]

private lemma weightedCountLE_eq (S : ℕ → Prop) (N : ℕ) :
    weightedCountLE S N = logWeightedCount S (N + 1) := by
  simp only [weightedCountLE, logWeightedCount, weightedIndicator,
    Nat.range_succ_eq_Icc_zero]

private lemma weightedCountLE_nonneg (S : ℕ → Prop) (N : ℕ) :
    0 ≤ weightedCountLE S N := by
  exact Finset.sum_nonneg fun n _ ↦ by
    simp only [weightedIndicator]
    split_ifs
    · exact Real.log_natCast_nonneg n
    · rfl

private lemma weightedCountLE_mono (S : ℕ → Prop) :
    Monotone (weightedCountLE S) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hmn)
    (fun _ _ _ ↦ by
      simp only [weightedIndicator]
      split_ifs
      · exact Real.log_natCast_nonneg _
      · rfl)

private lemma weightedCountLE_isEquivalent
    (S : ℕ → Prop) {A : ℝ} (hA : 0 < A)
    (hθ : (fun N ↦ logWeightedCount S N) ~[atTop]
      (fun N ↦ A * (N : ℝ))) :
    (fun N ↦ weightedCountLE S N) ~[atTop]
      (fun N ↦ A * (N : ℝ)) := by
  have hden : ∀ᶠ N : ℕ in atTop, A * (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact mul_ne_zero hA.ne' (by positivity)
  have hratio := (isEquivalent_iff_tendsto_one hden).mp hθ
  have hratioShift := hratio.comp (tendsto_add_atTop_nat 1)
  have hsucc : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds 1) := by
    have hbase : Tendsto (fun N : ℕ ↦ (1 : ℝ) + 1 / (N : ℝ))
        atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        tendsto_one_div_atTop_nhds_zero_nat
    apply Tendsto.congr' _ hbase
    filter_upwards [eventually_ge_atTop 1] with N hN
    field_simp
    norm_num [Nat.cast_add]
  apply (isEquivalent_iff_tendsto_one hden).mpr
  have heq :
      ((fun N : ℕ ↦ weightedCountLE S N) / (fun N : ℕ ↦ A * (N : ℝ))) =ᶠ[atTop]
        ((((fun N : ℕ ↦ logWeightedCount S N) / (fun N : ℕ ↦ A * (N : ℝ))) ∘
          (fun N : ℕ ↦ N + 1)) * (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ) / (N : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply]
    rw [weightedCountLE_eq]
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hN1 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  simpa only [one_mul] using Tendsto.congr' heq.symm (hratioShift.mul hsucc)

private lemma exists_weightedCountLE_linear_bound
    (S : ℕ → Prop)
    (hO : (fun N ↦ weightedCountLE S N) =O[atTop]
      (fun N ↦ (N : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      weightedCountLE S N ≤ C * (N + 1 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := hO.exists_pos
  rw [isBigOWith_iff, eventually_atTop] at hbound
  obtain ⟨N₀, hN₀⟩ := hbound
  let D := max C (weightedCountLE S N₀)
  have hD : 0 ≤ D := le_trans hC.le (le_max_left _ _)
  refine ⟨D, hD, fun N ↦ ?_⟩
  by_cases hNN₀ : N ≤ N₀
  · calc
      weightedCountLE S N ≤ weightedCountLE S N₀ := weightedCountLE_mono S hNN₀
      _ ≤ D := le_max_right _ _
      _ ≤ D * (N + 1 : ℝ) := by
        nth_rewrite 1 [← mul_one D]
        exact mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ (N : ℝ) + 1 by exact le_add_of_nonneg_left (Nat.cast_nonneg N)) hD
  · have hN₀N : N₀ ≤ N := Nat.le_of_lt (Nat.lt_of_not_ge hNN₀)
    have h := hN₀ N hN₀N
    rw [Real.norm_eq_abs, abs_of_nonneg (weightedCountLE_nonneg S N),
      Real.norm_natCast] at h
    calc
      weightedCountLE S N ≤ C * (N : ℝ) := h
      _ ≤ D * (N + 1 : ℝ) := by
        have hCD : C ≤ D := le_max_left _ _
        calc
          C * (N : ℝ) ≤ D * (N : ℝ) :=
            mul_le_mul_of_nonneg_right hCD (by positivity)
          _ ≤ D * (N + 1 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (show (N : ℝ) ≤ (N : ℝ) + 1 by exact le_add_of_nonneg_right zero_le_one) hD

private lemma countTwoLE_eq_invLog_weighted (S : ℕ → Prop) (N : ℕ) :
    countTwoLE S N =
      ∑ n ∈ Icc 0 N, (Real.log (n : ℝ))⁻¹ * weightedIndicator S n := by
  apply Finset.sum_congr rfl
  intro n hn
  simp only [weightedIndicator]
  by_cases hS : S n
  · by_cases hn2 : 2 ≤ n
    · have hlog : Real.log (n : ℝ) ≠ 0 := by
        exact Real.log_ne_zero_of_pos_of_ne_one (by positivity)
          (by exact_mod_cast (show n ≠ 1 by omega))
      simp [hS, hn2, hlog]
    · have hn : n = 0 ∨ n = 1 := by omega
      rcases hn with rfl | rfl <;> simp [hS]
  · simp [hS]

/-- The exact Abel-summation identity, before discarding the two invisible
indices `0` and `1`. -/
private lemma countTwoLE_eq_weighted_div_log_add_integral
    (S : ℕ → Prop) {N : ℕ} (hN : 2 ≤ N) :
    countTwoLE S N =
      weightedCountLE S N / Real.log (N : ℝ) +
        ∫ t in (2 : ℝ)..(N : ℝ),
          weightedCountLE S ⌊t⌋₊ / (t * Real.log t ^ 2) := by
  let c : ℕ → ℝ := weightedIndicator S
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ),
      DifferentiableAt ℝ (fun u : ℝ ↦ (Real.log u)⁻¹) t := by
    intro t ht
    exact Real.differentiableAt_inv_log (by linarith [ht.1])
      (by linarith [ht.1]) (by linarith [ht.1])
  have hint : IntegrableOn
      (deriv fun t : ℝ ↦ (Real.log t)⁻¹)
      (Set.Icc (2 : ℝ) (N : ℝ)) := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦
      ContinuousWithinAt.congr ?_
        (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
      · linarith [ht.1]
      · linarith [ht.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hAbel := sum_mul_eq_sub_integral_mul₁ c
    (f := fun t : ℝ ↦ (Real.log t)⁻¹)
    (by simp [c]) (by simp [c]) (N : ℝ) hdiff hint
  rw [← intervalIntegral.integral_of_le hNreal] at hAbel
  have hsum (m : ℕ) : ∑ n ∈ Icc 0 m, c n = weightedCountLE S m := by
    rfl
  rw [Nat.floor_natCast, hsum] at hAbel
  rw [countTwoLE_eq_invLog_weighted, show weightedIndicator S = c by rfl]
  calc
    ∑ n ∈ Icc 0 N, (Real.log (n : ℝ))⁻¹ * c n =
        (Real.log (N : ℝ))⁻¹ * weightedCountLE S N -
          ∫ t in (2 : ℝ)..(N : ℝ),
            deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t * weightedCountLE S ⌊t⌋₊ := hAbel
    _ = weightedCountLE S N / Real.log (N : ℝ) +
          ∫ t in (2 : ℝ)..(N : ℝ),
            weightedCountLE S ⌊t⌋₊ / (t * Real.log t ^ 2) := by
      rw [sub_eq_add_neg, ← intervalIntegral.integral_neg]
      congr 1
      · simp only [div_eq_mul_inv]
        ring
      · apply intervalIntegral.integral_congr
        intro t ht
        have htIcc : t ∈ Set.Icc (2 : ℝ) (N : ℝ) := by
          simpa [Set.uIcc_of_le hNreal] using ht
        change -(deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t * weightedCountLE S ⌊t⌋₊) =
          weightedCountLE S ⌊t⌋₊ / (t * Real.log t ^ 2)
        rw [Real.deriv_inv_log_apply]
        have ht0 : t ≠ 0 := by linarith [htIcc.1]
        have hlog : Real.log t ≠ 0 :=
          Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
            (by linarith [htIcc.1])
        field_simp

/-! ## Counts with multiplicities -/

/-- The logarithmically weighted count of a natural-valued multiplicity
function below `N`. -/
def coefficientLogWeightedCount (a : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (a n : ℝ) * Real.log (n : ℝ)

/-- The unweighted count, with multiplicities, below `N`. -/
def coefficientCount (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ range N, a n

private def coefficientWeightedIndicator (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a n : ℝ) * Real.log (n : ℝ)

private def coefficientWeightedCountLE (a : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 0 N, coefficientWeightedIndicator a n

private def coefficientCountTwoLE (a : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 0 N, if 2 ≤ n then (a n : ℝ) else 0

@[simp] private lemma coefficientWeightedIndicator_zero (a : ℕ → ℕ) :
    coefficientWeightedIndicator a 0 = 0 := by
  simp [coefficientWeightedIndicator]

@[simp] private lemma coefficientWeightedIndicator_one (a : ℕ → ℕ) :
    coefficientWeightedIndicator a 1 = 0 := by
  simp [coefficientWeightedIndicator]

private lemma coefficientWeightedCountLE_eq (a : ℕ → ℕ) (N : ℕ) :
    coefficientWeightedCountLE a N = coefficientLogWeightedCount a (N + 1) := by
  simp only [coefficientWeightedCountLE, coefficientLogWeightedCount,
    coefficientWeightedIndicator, Nat.range_succ_eq_Icc_zero]

private lemma coefficientWeightedCountLE_nonneg (a : ℕ → ℕ) (N : ℕ) :
    0 ≤ coefficientWeightedCountLE a N := by
  exact Finset.sum_nonneg fun n _ ↦
    mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)

private lemma coefficientWeightedCountLE_mono (a : ℕ → ℕ) :
    Monotone (coefficientWeightedCountLE a) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hmn)
    (fun k _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg k))

private lemma coefficientCountTwoLE_eq_invLog_weighted (a : ℕ → ℕ) (N : ℕ) :
    coefficientCountTwoLE a N =
      ∑ n ∈ Icc 0 N,
        (Real.log (n : ℝ))⁻¹ * coefficientWeightedIndicator a n := by
  apply Finset.sum_congr rfl
  intro n hn
  simp only [coefficientWeightedIndicator]
  by_cases hn2 : 2 ≤ n
  · have hlog : Real.log (n : ℝ) ≠ 0 := by
      exact Real.log_ne_zero_of_pos_of_ne_one (by positivity)
        (by exact_mod_cast (show n ≠ 1 by omega))
    rw [if_pos hn2]
    field_simp [hlog]
  · have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with rfl | rfl <;> simp

private lemma coefficientCountTwoLE_eq_weighted_div_log_add_integral
    (a : ℕ → ℕ) {N : ℕ} (hN : 2 ≤ N) :
    coefficientCountTwoLE a N =
      coefficientWeightedCountLE a N / Real.log (N : ℝ) +
        ∫ t in (2 : ℝ)..(N : ℝ),
          coefficientWeightedCountLE a ⌊t⌋₊ / (t * Real.log t ^ 2) := by
  let c : ℕ → ℝ := coefficientWeightedIndicator a
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ),
      DifferentiableAt ℝ (fun u : ℝ ↦ (Real.log u)⁻¹) t := by
    intro t ht
    exact Real.differentiableAt_inv_log (by linarith [ht.1])
      (by linarith [ht.1]) (by linarith [ht.1])
  have hint : IntegrableOn
      (deriv fun t : ℝ ↦ (Real.log t)⁻¹)
      (Set.Icc (2 : ℝ) (N : ℝ)) := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦
      ContinuousWithinAt.congr ?_
        (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
      · linarith [ht.1]
      · linarith [ht.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hAbel := sum_mul_eq_sub_integral_mul₁ c
    (f := fun t : ℝ ↦ (Real.log t)⁻¹)
    (by simp [c]) (by simp [c]) (N : ℝ) hdiff hint
  rw [← intervalIntegral.integral_of_le hNreal] at hAbel
  have hsum (m : ℕ) :
      ∑ n ∈ Icc 0 m, c n = coefficientWeightedCountLE a m := by
    rfl
  rw [Nat.floor_natCast, hsum] at hAbel
  rw [coefficientCountTwoLE_eq_invLog_weighted,
    show coefficientWeightedIndicator a = c by rfl]
  calc
    ∑ n ∈ Icc 0 N, (Real.log (n : ℝ))⁻¹ * c n =
        (Real.log (N : ℝ))⁻¹ * coefficientWeightedCountLE a N -
          ∫ t in (2 : ℝ)..(N : ℝ),
            deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t *
              coefficientWeightedCountLE a ⌊t⌋₊ := hAbel
    _ = coefficientWeightedCountLE a N / Real.log (N : ℝ) +
          ∫ t in (2 : ℝ)..(N : ℝ),
            coefficientWeightedCountLE a ⌊t⌋₊ / (t * Real.log t ^ 2) := by
      rw [sub_eq_add_neg, ← intervalIntegral.integral_neg]
      congr 1
      · simp only [div_eq_mul_inv]
        ring
      · apply intervalIntegral.integral_congr
        intro t ht
        have htIcc : t ∈ Set.Icc (2 : ℝ) (N : ℝ) := by
          simpa [Set.uIcc_of_le hNreal] using ht
        change -(deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t *
            coefficientWeightedCountLE a ⌊t⌋₊) =
          coefficientWeightedCountLE a ⌊t⌋₊ / (t * Real.log t ^ 2)
        rw [Real.deriv_inv_log_apply]
        have ht0 : t ≠ 0 := by linarith [htIcc.1]
        have hlog : Real.log t ≠ 0 :=
          Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
            (by linarith [htIcc.1])
        field_simp

private lemma coefficientWeightedCountLE_isEquivalent
    (a : ℕ → ℕ) {A : ℝ} (hA : 0 < A)
    (hθ : (fun N ↦ coefficientLogWeightedCount a N) ~[atTop]
      (fun N ↦ A * (N : ℝ))) :
    (fun N ↦ coefficientWeightedCountLE a N) ~[atTop]
      (fun N ↦ A * (N : ℝ)) := by
  have hden : ∀ᶠ N : ℕ in atTop, A * (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact mul_ne_zero hA.ne' (by positivity)
  have hratio := (isEquivalent_iff_tendsto_one hden).mp hθ
  have hratioShift := hratio.comp (tendsto_add_atTop_nat 1)
  have hsucc : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds 1) := by
    have hbase : Tendsto (fun N : ℕ ↦ (1 : ℝ) + 1 / (N : ℝ))
        atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        tendsto_one_div_atTop_nhds_zero_nat
    apply Tendsto.congr' _ hbase
    filter_upwards [eventually_ge_atTop 1] with N hN
    field_simp
    norm_num [Nat.cast_add]
  apply (isEquivalent_iff_tendsto_one hden).mpr
  have heq :
      ((fun N : ℕ ↦ coefficientWeightedCountLE a N) /
          (fun N : ℕ ↦ A * (N : ℝ))) =ᶠ[atTop]
        ((((fun N : ℕ ↦ coefficientLogWeightedCount a N) /
            (fun N : ℕ ↦ A * (N : ℝ))) ∘ (fun N : ℕ ↦ N + 1)) *
          (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ) / (N : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply]
    rw [coefficientWeightedCountLE_eq]
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hN1 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  simpa only [one_mul] using Tendsto.congr' heq.symm (hratioShift.mul hsucc)

private lemma exists_coefficientWeightedCountLE_linear_bound
    (a : ℕ → ℕ)
    (hO : (fun N ↦ coefficientWeightedCountLE a N) =O[atTop]
      (fun N ↦ (N : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      coefficientWeightedCountLE a N ≤ C * (N + 1 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := hO.exists_pos
  rw [isBigOWith_iff, eventually_atTop] at hbound
  obtain ⟨N₀, hN₀⟩ := hbound
  let D := max C (coefficientWeightedCountLE a N₀)
  have hD : 0 ≤ D := le_trans hC.le (le_max_left _ _)
  refine ⟨D, hD, fun N ↦ ?_⟩
  by_cases hNN₀ : N ≤ N₀
  · calc
      coefficientWeightedCountLE a N ≤ coefficientWeightedCountLE a N₀ :=
        coefficientWeightedCountLE_mono a hNN₀
      _ ≤ D := le_max_right _ _
      _ ≤ D * (N + 1 : ℝ) := by
        nth_rewrite 1 [← mul_one D]
        exact mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ (N : ℝ) + 1 by
            exact le_add_of_nonneg_left (Nat.cast_nonneg N)) hD
  · have hN₀N : N₀ ≤ N := Nat.le_of_lt (Nat.lt_of_not_ge hNN₀)
    have h := hN₀ N hN₀N
    rw [Real.norm_eq_abs, abs_of_nonneg (coefficientWeightedCountLE_nonneg a N),
      Real.norm_natCast] at h
    calc
      coefficientWeightedCountLE a N ≤ C * (N : ℝ) := h
      _ ≤ D * (N + 1 : ℝ) := by
        have hCD : C ≤ D := le_max_left _ _
        calc
          C * (N : ℝ) ≤ D * (N : ℝ) :=
            mul_le_mul_of_nonneg_right hCD (by positivity)
          _ ≤ D * (N + 1 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (show (N : ℝ) ≤ (N : ℝ) + 1 by
                exact le_add_of_nonneg_right zero_le_one) hD

private def coefficientAbelRemainder (a : ℕ → ℕ) (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x,
    coefficientWeightedCountLE a ⌊t⌋₊ / (t * Real.log t ^ 2)

private lemma intervalIntegrable_coefficientAbelIntegrand
    (a : ℕ → ℕ) {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable
      (fun t : ℝ ↦ coefficientWeightedCountLE a ⌊t⌋₊ /
        (t * Real.log t ^ 2)) volume 2 x := by
  let c : ℕ → ℝ := coefficientWeightedIndicator a
  have hderiv : IntegrableOn
      (deriv fun t : ℝ ↦ (Real.log t)⁻¹) (Set.Icc (2 : ℝ) x) := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦
      ContinuousWithinAt.congr ?_
        (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
      · linarith [ht.1]
      · linarith [ht.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  have hmul := integrableOn_mul_sum_Icc c (m := 0) (a := (2 : ℝ))
    (by norm_num) hderiv
  refine hmul.neg.congr_fun_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
  change -(deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =
    coefficientWeightedCountLE a ⌊t⌋₊ / (t * Real.log t ^ 2)
  have hsum : ∑ k ∈ Icc 0 ⌊t⌋₊, c k = coefficientWeightedCountLE a ⌊t⌋₊ := rfl
  rw [hsum, Real.deriv_inv_log_apply]
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  field_simp

private lemma coefficientAbelRemainder_isBigO
    (a : ℕ → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hlinear : ∀ N : ℕ,
      coefficientWeightedCountLE a N ≤ C * (N + 1 : ℝ)) :
    coefficientAbelRemainder a =O[atTop]
      (fun x : ℝ ↦ x / Real.log x ^ 2) := by
  refine (IsBigO.of_bound (2 * C) ?_).trans
    Chebyshev.integral_one_div_log_sq_isBigO
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
  simp only [coefficientAbelRemainder, Real.norm_eq_abs]
  calc
    |∫ t in (2 : ℝ)..x,
        coefficientWeightedCountLE a ⌊t⌋₊ / (t * Real.log t ^ 2)|
        ≤ ∫ t in (2 : ℝ)..x,
          |coefficientWeightedCountLE a ⌊t⌋₊ / (t * Real.log t ^ 2)| :=
      intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ t in (2 : ℝ)..x, (2 * C) * (1 / Real.log t ^ 2) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (intervalIntegrable_coefficientAbelIntegrand a (by linarith)).abs
      · exact (Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)).const_mul _
      · intro t ht
        have htpos : 0 < t := by linarith [ht.1]
        have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
        have hfloor : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le htpos.le
        have hW := hlinear ⌊t⌋₊
        have hWnonneg := coefficientWeightedCountLE_nonneg a ⌊t⌋₊
        rw [abs_of_nonneg (div_nonneg hWnonneg (by positivity))]
        have hstep : C * ((⌊t⌋₊ : ℕ) + 1 : ℝ) ≤ 2 * C * t := by
          have haux : (((⌊t⌋₊ : ℕ) : ℝ) + 1) ≤ 2 * t := by
            linarith [hfloor, ht.1]
          have hmul := mul_le_mul_of_nonneg_left haux hC
          simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
        calc
          coefficientWeightedCountLE a ⌊t⌋₊ / (t * Real.log t ^ 2)
              ≤ (C * ((⌊t⌋₊ : ℕ) + 1 : ℝ)) /
                  (t * Real.log t ^ 2) :=
            div_le_div_of_nonneg_right hW (by positivity)
          _ ≤ (2 * C * t) / (t * Real.log t ^ 2) :=
            div_le_div_of_nonneg_right hstep (by positivity)
          _ = (2 * C) * (1 / Real.log t ^ 2) := by field_simp
    _ = (2 * C) * |∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2| := by
      rw [intervalIntegral.integral_const_mul, abs_of_nonneg]
      exact intervalIntegral.integral_nonneg (by linarith) fun t _ ↦ by positivity

private lemma coefficientAbelRemainder_isLittleO
    (a : ℕ → ℕ)
    (hO : (fun N ↦ coefficientWeightedCountLE a N) =O[atTop]
      (fun N ↦ (N : ℝ))) :
    coefficientAbelRemainder a =o[atTop]
      (fun x : ℝ ↦ x / Real.log x) := by
  obtain ⟨C, hC, hlinear⟩ := exists_coefficientWeightedCountLE_linear_bound a hO
  refine (coefficientAbelRemainder_isBigO a hC hlinear).trans_isLittleO ?_
  refine isLittleO_iff_tendsto' (by simp) |>.mpr ?_
  refine Tendsto.congr' (f₁ := fun x ↦ (Real.log x)⁻¹) ?_
    Real.tendsto_log_atTop.inv_tendsto_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by linarith
  have hlog : Real.log x ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  field_simp

private lemma const_isLittleO_nat_div_log (K : ℝ) :
    (fun _ : ℕ ↦ K) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ)) := by
  have hlog : (fun N : ℕ ↦ Real.log (N : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hzero : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) = 0 → (N : ℝ) = 0 := by
    filter_upwards [eventually_ge_atTop 2] with N hN hlogzero
    have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
    exact (ne_of_gt (Real.log_pos hNreal) hlogzero).elim
  have hinv : (fun N : ℕ ↦ ((N : ℝ))⁻¹) =o[atTop]
      (fun N : ℕ ↦ (Real.log (N : ℝ))⁻¹) :=
    hlog.inv_rev hzero
  have hone : (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ)) := by
    refine (hinv.mul_isBigO (isBigO_refl (fun N : ℕ ↦ (N : ℝ)) atTop)).congr' ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      simp [Nat.ne_of_gt hN]
    · exact Eventually.of_forall fun N ↦ by
        simp only [div_eq_mul_inv]
        ring
  exact (isBigO_const_const K one_ne_zero atTop).trans_isLittleO hone

private lemma coefficientCountTwoLE_sub_count_bound
    (a : ℕ → ℕ) (d : ℕ) (ha : ∀ n, a n ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    |(coefficientCount a N : ℝ) - coefficientCountTwoLE a N| ≤ 3 * d := by
  let f : ℕ → ℝ := fun n ↦ (a n : ℝ)
  have htwo : coefficientCountTwoLE a N = ∑ n ∈ Finset.Icc 2 N, f n := by
    unfold coefficientCountTwoLE
    calc
      (∑ n ∈ Finset.Icc 0 N, if 2 ≤ n then (a n : ℝ) else 0) =
          ∑ n ∈ (Finset.Icc 0 N).filter (2 ≤ ·), f n := by
        rw [sum_filter]
      _ = ∑ n ∈ Finset.Icc 2 N, f n := by
        apply sum_congr
        · ext n
          simp only [mem_filter, Finset.mem_Icc]
          omega
        · intro n hn
          rfl
  have hIcc : ∑ n ∈ Icc 2 N, f n = f N + ∑ n ∈ Ico 2 N, f n := by
    rw [← Ico_add_one_right_eq_Icc, ← insert_Ico_right_eq_Ico_add_one hN,
      sum_insert right_notMem_Ico]
  have hIco : ∑ n ∈ Ico 2 N, f n =
      ∑ n ∈ range N, f n - (f 0 + f 1) := by
    rw [Finset.sum_Ico_eq_sub f hN]
    change (∑ n ∈ range N, f n) - (∑ n ∈ range 2, f n) = _
    norm_num [Finset.sum_range_succ, f]
  have hraw : (coefficientCount a N : ℝ) = ∑ n ∈ range N, f n := by
    simp [coefficientCount, f]
  rw [htwo, hIcc, hIco, hraw]
  have h0 : f 0 ≤ d := by change (a 0 : ℝ) ≤ (d : ℝ); exact_mod_cast ha 0
  have h1 : f 1 ≤ d := by change (a 1 : ℝ) ≤ (d : ℝ); exact_mod_cast ha 1
  have hNN : f N ≤ d := by change (a N : ℝ) ≤ (d : ℝ); exact_mod_cast ha N
  have h0nonneg : 0 ≤ f 0 := by positivity
  have h1nonneg : 0 ≤ f 1 := by positivity
  have hNnonneg : 0 ≤ f N := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-- Abel summation transfers a positive linear asymptotic for a
logarithmically weighted count with uniformly bounded natural multiplicities
to the corresponding unweighted count. -/
theorem coefficientCount_isEquivalent_of_logWeighted
    (a : ℕ → ℕ) (d : ℕ) (ha : ∀ n, a n ≤ d)
    {A : ℝ} (hA : 0 < A)
    (hθ : (fun N ↦ coefficientLogWeightedCount a N) ~[atTop]
      (fun N ↦ A * (N : ℝ))) :
    (fun N ↦ (coefficientCount a N : ℝ)) ~[atTop]
      (fun N ↦ A * (N : ℝ) / Real.log (N : ℝ)) := by
  have hW := coefficientWeightedCountLE_isEquivalent a hA hθ
  have hWO : (fun N ↦ coefficientWeightedCountLE a N) =O[atTop]
      (fun N ↦ (N : ℝ)) := by
    refine hW.isBigO.trans (IsBigO.of_bound |A| ?_)
    exact Eventually.of_forall fun N ↦ by
      simp [Real.norm_eq_abs, norm_mul]
  have hmain : (fun N ↦ coefficientWeightedCountLE a N /
        Real.log (N : ℝ)) ~[atTop]
      (fun N ↦ A * (N : ℝ) / Real.log (N : ℝ)) := by
    have hdiv := hW.div (IsEquivalent.refl :
      (fun N : ℕ ↦ Real.log (N : ℝ)) ~[atTop]
        (fun N : ℕ ↦ Real.log (N : ℝ)))
    change (fun N ↦ coefficientWeightedCountLE a N / Real.log (N : ℝ)) ~[atTop]
      (fun N ↦ A * (N : ℝ) / Real.log (N : ℝ)) at hdiv
    exact hdiv
  have hremBase : (fun N : ℕ ↦ coefficientAbelRemainder a (N : ℝ)) =o[atTop]
      (fun N ↦ (N : ℝ) / Real.log (N : ℝ)) := by
    simpa [Function.comp_def] using
      (coefficientAbelRemainder_isLittleO a hWO).comp_tendsto
        tendsto_natCast_atTop_atTop
  have hscale : (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ)) =O[atTop]
      (fun N ↦ A * (N : ℝ) / Real.log (N : ℝ)) := by
    have h := (isBigO_refl (fun N : ℕ ↦ (N : ℝ) /
      Real.log (N : ℝ)) atTop).const_mul_right hA.ne'
    refine h.congr' (EventuallyEq.rfl) ?_
    exact Eventually.of_forall fun N ↦ by ring
  have hrem := hremBase.trans_isBigO hscale
  have htwo : (fun N ↦ coefficientCountTwoLE a N) ~[atTop]
      (fun N ↦ A * (N : ℝ) / Real.log (N : ℝ)) := by
    refine (hmain.add_isLittleO hrem).congr_left ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (coefficientCountTwoLE_eq_weighted_div_log_add_integral a hN).symm
  have hdiffBase :
      (fun N ↦ (coefficientCount a N : ℝ) - coefficientCountTwoLE a N) =o[atTop]
        (fun N ↦ (N : ℝ) / Real.log (N : ℝ)) := by
    refine (IsBigO.of_bound (3 * d : ℝ) ?_).trans_isLittleO
      (const_isLittleO_nat_div_log 1)
    filter_upwards [eventually_ge_atTop 2] with N hN
    simpa only [Real.norm_eq_abs, norm_one, mul_one] using
      coefficientCountTwoLE_sub_count_bound a d ha hN
  refine (hdiffBase.trans_isBigO hscale).add_isEquivalent htwo |>.congr_left ?_
  exact Eventually.of_forall fun N ↦ by simp only [Pi.add_apply]; ring

/-- Ratio form, normalized to leading constant one. -/
theorem coefficientCount_isEquivalent_of_logWeighted_ratio_one
    (a : ℕ → ℕ) (d : ℕ) (ha : ∀ n, a n ≤ d)
    (hθ : Tendsto
      (fun N ↦ coefficientLogWeightedCount a N / (N : ℝ))
      atTop (nhds 1)) :
    (fun N ↦ (coefficientCount a N : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) / Real.log (N : ℝ)) := by
  have hweighted : (fun N ↦ coefficientLogWeightedCount a N) ~[atTop]
      (fun N ↦ (1 : ℝ) * (N : ℝ)) := by
    simpa only [one_mul] using isEquivalent_of_tendsto_one hθ
  simpa only [one_mul] using
    coefficientCount_isEquivalent_of_logWeighted a d ha one_pos hweighted

/-- Predicate-valued specialization of
`coefficientCount_isEquivalent_of_logWeighted`. -/
theorem predicateCount_isEquivalent_of_logWeightedCount
    (S : ℕ → Prop) {A : ℝ} (hA : 0 < A)
    (hθ : (fun N ↦ logWeightedCount S N) ~[atTop]
      (fun N ↦ A * (N : ℝ))) :
    (fun N ↦ (predicateCount S N : ℝ)) ~[atTop]
      (fun N ↦ A * (N : ℝ) / Real.log (N : ℝ)) := by
  let a : ℕ → ℕ := fun n ↦ if S n then 1 else 0
  have ha : ∀ n, a n ≤ 1 := by
    intro n
    simp only [a]
    split <;> omega
  have hlog (N : ℕ) :
      coefficientLogWeightedCount a N = logWeightedCount S N := by
    apply sum_congr rfl
    intro n hn
    simp [a]
  have hcount (N : ℕ) : coefficientCount a N = predicateCount S N := by
    unfold coefficientCount predicateCount
    simp [a, Finset.sum_boole]
  have hθ' : (fun N ↦ coefficientLogWeightedCount a N) ~[atTop]
      (fun N ↦ A * (N : ℝ)) := by
    rw [show (fun N ↦ coefficientLogWeightedCount a N) =
      (fun N ↦ logWeightedCount S N) from funext hlog]
    exact hθ
  simpa only [hcount] using
    coefficientCount_isEquivalent_of_logWeighted a 1 ha hA hθ'

/-- Alias with the weighted count named first. -/
theorem logWeightedCount_isEquivalent_predicateCount
    (S : ℕ → Prop) {A : ℝ} (hA : 0 < A)
    (hθ : (fun N ↦ logWeightedCount S N) ~[atTop]
      (fun N ↦ A * (N : ℝ))) :
    (fun N ↦ (predicateCount S N : ℝ)) ~[atTop]
      (fun N ↦ A * (N : ℝ) / Real.log (N : ℝ)) :=
  predicateCount_isEquivalent_of_logWeightedCount S hA hθ

end

end Erdos980.NaturalChebotarev
