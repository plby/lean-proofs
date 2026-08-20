/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.CountingConversion
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

/-!
# Removing logarithmic weights from a nonnegative counting function

This file supplies the Abel-summation step omitted from `CountingConversion`.
Because both sums use the same closed interval `Icc 2 n`, no pointwise bound
on the multiplicities is needed.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open Asymptotics Filter Finset MeasureTheory Set

noncomputable section

open scoped BigOperators Topology

private def extendedWeighted (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  if 2 ≤ m then a m * Real.log (m : ℝ) else 0

@[simp] private lemma extendedWeighted_zero (a : ℕ → ℝ) :
    extendedWeighted a 0 = 0 := by
  simp [extendedWeighted]

@[simp] private lemma extendedWeighted_one (a : ℕ → ℝ) :
    extendedWeighted a 1 = 0 := by
  simp [extendedWeighted]

private lemma sum_extendedWeighted (a : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ Icc 0 n, extendedWeighted a m = multiplicityChebyshev a n := by
  unfold extendedWeighted multiplicityChebyshev
  calc
    (∑ m ∈ Finset.Icc 0 n, if 2 ≤ m then a m * Real.log (m : ℝ) else 0) =
        ∑ m ∈ (Finset.Icc 0 n).filter (2 ≤ ·), a m * Real.log (m : ℝ) := by
      rw [sum_filter]
    _ = ∑ m ∈ Finset.Icc 2 n, a m * Real.log (m : ℝ) := by
      apply sum_congr
      · ext m
        simp only [mem_filter, Finset.mem_Icc]
        omega
      · intro m hm
        rfl

private lemma sum_invLog_extendedWeighted (a : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ Icc 0 n, (Real.log (m : ℝ))⁻¹ * extendedWeighted a m =
      multiplicityCount a n := by
  rw [multiplicityCount]
  calc
    (∑ m ∈ Icc 0 n, (Real.log (m : ℝ))⁻¹ * extendedWeighted a m) =
        ∑ m ∈ Icc 0 n, if 2 ≤ m then a m else 0 := by
      apply sum_congr rfl
      intro m hm
      by_cases hm2 : 2 ≤ m
      · have hlog : Real.log (m : ℝ) ≠ 0 :=
          Real.log_ne_zero_of_pos_of_ne_one (by positivity)
            (by exact_mod_cast (show m ≠ 1 by omega))
        simp only [extendedWeighted, if_pos hm2]
        field_simp
      · simp [extendedWeighted, hm2]
    _ = ∑ m ∈ (Finset.Icc 0 n).filter (2 ≤ ·), a m := by
      rw [sum_filter]
    _ = ∑ m ∈ Finset.Icc 2 n, a m := by
      apply sum_congr
      · ext m
        simp only [mem_filter, Finset.mem_Icc]
        omega
      · intro m hm
        rfl

/-- The integral remainder in the Abel-summation formula. -/
def multiplicityAbelRemainder (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x,
    multiplicityChebyshev a ⌊t⌋₊ / (t * Real.log t ^ 2)

/-- Exact finite Abel summation for the logarithmically weighted sequence. -/
theorem multiplicityCount_eq_weighted_div_log_add_remainder
    (a : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    multiplicityCount a n =
      multiplicityChebyshev a n / endpointLog n +
        multiplicityAbelRemainder a n := by
  let c : ℕ → ℝ := extendedWeighted a
  have hnReal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) (n : ℝ),
      DifferentiableAt ℝ (fun u : ℝ ↦ (Real.log u)⁻¹) t := by
    intro t ht
    exact Real.differentiableAt_inv_log (by linarith [ht.1])
      (by linarith [ht.1]) (by linarith [ht.1])
  have hint : IntegrableOn
      (deriv fun t : ℝ ↦ (Real.log t)⁻¹)
      (Set.Icc (2 : ℝ) (n : ℝ)) := by
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
    (by simp [c]) (by simp [c]) (n : ℝ) hdiff hint
  rw [← intervalIntegral.integral_of_le hnReal] at hAbel
  have hsum (m : ℕ) : ∑ k ∈ Finset.Icc 0 m, c k =
      multiplicityChebyshev a m := by
    simpa [c] using sum_extendedWeighted a m
  rw [Nat.floor_natCast] at hAbel
  simp_rw [hsum] at hAbel
  rw [← sum_invLog_extendedWeighted a n, show extendedWeighted a = c by rfl]
  calc
    ∑ m ∈ Icc 0 n, (Real.log (m : ℝ))⁻¹ * c m =
        (Real.log (n : ℝ))⁻¹ * multiplicityChebyshev a n -
          ∫ t in (2 : ℝ)..(n : ℝ),
            deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t *
              multiplicityChebyshev a ⌊t⌋₊ := hAbel
    _ = multiplicityChebyshev a n / endpointLog n +
          multiplicityAbelRemainder a n := by
      rw [sub_eq_add_neg, ← intervalIntegral.integral_neg]
      congr 1
      · simp only [endpointLog, div_eq_mul_inv]
        ring
      · apply intervalIntegral.integral_congr
        intro t ht
        have htIcc : t ∈ Set.Icc (2 : ℝ) (n : ℝ) := by
          simpa [Set.uIcc_of_le hnReal] using ht
        change -(deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t *
            multiplicityChebyshev a ⌊t⌋₊) =
          multiplicityChebyshev a ⌊t⌋₊ / (t * Real.log t ^ 2)
        rw [Real.deriv_inv_log_apply]
        have ht0 : t ≠ 0 := by linarith [htIcc.1]
        have hlog : Real.log t ≠ 0 :=
          Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
            (by linarith [htIcc.1])
        field_simp

private lemma multiplicityChebyshev_mono {a : ℕ → ℝ}
    (ha : ∀ m, 0 ≤ a m) : Monotone (multiplicityChebyshev a) := by
  intro m n hmn
  apply Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hmn)
  intro k hk hnot
  have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
  exact mul_nonneg (ha k) (Real.log_nonneg (by exact_mod_cast hk2.trans' (by norm_num)))

private lemma exists_multiplicityChebyshev_linear_bound
    {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m)
    (hO : multiplicityChebyshev a =O[atTop] (fun n ↦ (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      multiplicityChebyshev a n ≤ C * (n + 1 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := hO.exists_pos
  rw [isBigOWith_iff, eventually_atTop] at hbound
  obtain ⟨n₀, hn₀⟩ := hbound
  let D := max C (multiplicityChebyshev a n₀)
  have hD : 0 ≤ D := le_trans hC.le (le_max_left _ _)
  refine ⟨D, hD, fun n ↦ ?_⟩
  by_cases hnn₀ : n ≤ n₀
  · calc
      multiplicityChebyshev a n ≤ multiplicityChebyshev a n₀ :=
        multiplicityChebyshev_mono ha hnn₀
      _ ≤ D := le_max_right _ _
      _ ≤ D * (n + 1 : ℝ) := by
        nth_rewrite 1 [← mul_one D]
        exact mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ (n : ℝ) + 1 by
            exact le_add_of_nonneg_left (Nat.cast_nonneg n)) hD
  · have hn₀n : n₀ ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hnn₀)
    have h := hn₀ n hn₀n
    rw [Real.norm_eq_abs, abs_of_nonneg (multiplicityChebyshev_nonneg ha n),
      Real.norm_natCast] at h
    calc
      multiplicityChebyshev a n ≤ C * (n : ℝ) := h
      _ ≤ D * (n + 1 : ℝ) := by
        calc
          C * (n : ℝ) ≤ D * (n : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg n)
          _ ≤ D * (n + 1 : ℝ) := by
            exact mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right zero_le_one) hD

private lemma intervalIntegrable_multiplicityAbelIntegrand
    (a : ℕ → ℝ) {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable
      (fun t : ℝ ↦ multiplicityChebyshev a ⌊t⌋₊ /
        (t * Real.log t ^ 2)) volume 2 x := by
  let c : ℕ → ℝ := extendedWeighted a
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
      ∑ m ∈ Icc 0 ⌊t⌋₊, c m) =
    multiplicityChebyshev a ⌊t⌋₊ / (t * Real.log t ^ 2)
  rw [show (∑ m ∈ Icc 0 ⌊t⌋₊, c m) =
      multiplicityChebyshev a ⌊t⌋₊ by
        simpa [c] using sum_extendedWeighted a ⌊t⌋₊,
    Real.deriv_inv_log_apply]
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  field_simp

private lemma multiplicityAbelRemainder_isBigO
    {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m) {C : ℝ} (hC : 0 ≤ C)
    (hlinear : ∀ n : ℕ, multiplicityChebyshev a n ≤ C * (n + 1 : ℝ)) :
    multiplicityAbelRemainder a =O[atTop]
      (fun x : ℝ ↦ x / Real.log x ^ 2) := by
  refine (IsBigO.of_bound (2 * C) ?_).trans
    Chebyshev.integral_one_div_log_sq_isBigO
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
  simp only [multiplicityAbelRemainder, Real.norm_eq_abs]
  calc
    |∫ t in (2 : ℝ)..x,
        multiplicityChebyshev a ⌊t⌋₊ / (t * Real.log t ^ 2)|
        ≤ ∫ t in (2 : ℝ)..x,
          |multiplicityChebyshev a ⌊t⌋₊ / (t * Real.log t ^ 2)| :=
      intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ t in (2 : ℝ)..x, (2 * C) * (1 / Real.log t ^ 2) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (intervalIntegrable_multiplicityAbelIntegrand a (by linarith)).abs
      · exact (Chebyshev.intervalIntegrable_one_div_log_sq
          (by norm_num) (by linarith)).const_mul _
      · intro t ht
        have htpos : 0 < t := by linarith [ht.1]
        have hfloor : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le htpos.le
        have hW := hlinear ⌊t⌋₊
        have hWnonneg := multiplicityChebyshev_nonneg ha ⌊t⌋₊
        rw [abs_of_nonneg (div_nonneg hWnonneg (by positivity))]
        have hstep : C * ((⌊t⌋₊ : ℕ) + 1 : ℝ) ≤ 2 * C * t := by
          have haux : (((⌊t⌋₊ : ℕ) : ℝ) + 1) ≤ 2 * t := by
            linarith [hfloor, ht.1]
          have hmul := mul_le_mul_of_nonneg_left haux hC
          simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
        calc
          multiplicityChebyshev a ⌊t⌋₊ / (t * Real.log t ^ 2)
              ≤ (C * ((⌊t⌋₊ : ℕ) + 1 : ℝ)) /
                  (t * Real.log t ^ 2) :=
            div_le_div_of_nonneg_right hW (by positivity)
          _ ≤ (2 * C * t) / (t * Real.log t ^ 2) :=
            div_le_div_of_nonneg_right hstep (by positivity)
          _ = (2 * C) * (1 / Real.log t ^ 2) := by field_simp
    _ = (2 * C) * |∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2| := by
      rw [intervalIntegral.integral_const_mul, abs_of_nonneg]
      exact intervalIntegral.integral_nonneg (by linarith) fun t _ ↦ by positivity

private lemma multiplicityAbelRemainder_isLittleO
    {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m)
    (hO : multiplicityChebyshev a =O[atTop] (fun n ↦ (n : ℝ))) :
    multiplicityAbelRemainder a =o[atTop]
      (fun x : ℝ ↦ x / Real.log x) := by
  obtain ⟨C, hC, hlinear⟩ := exists_multiplicityChebyshev_linear_bound ha hO
  refine (multiplicityAbelRemainder_isBigO ha hC hlinear).trans_isLittleO ?_
  refine isLittleO_iff_tendsto' (by simp) |>.mpr ?_
  refine Tendsto.congr' (f₁ := fun x ↦ (Real.log x)⁻¹) ?_
    Real.tendsto_log_atTop.inv_tendsto_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by linarith
  have hlog : Real.log x ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  field_simp

/-- Generic Abel/partial-summation theorem for nonnegative multiplicities.

If the logarithmically weighted sum is asymptotic to `n`, then the
unweighted sum is asymptotic to `n / log n`. -/
theorem multiplicityCount_isEquivalent_of_multiplicityChebyshev
    {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m)
    (hweighted : multiplicityChebyshev a ~[atTop] (fun n ↦ (n : ℝ))) :
    multiplicityCount a ~[atTop] pntScale 1 := by
  have hmain : (fun n ↦ multiplicityChebyshev a n / endpointLog n) ~[atTop]
      pntScale 1 := by
    rw [pntScale]
    have hd := hweighted.div
      (IsEquivalent.refl : endpointLog ~[atTop] endpointLog)
    have hdl := hd.congr_left
      (w := fun n ↦ multiplicityChebyshev a n / endpointLog n)
      (Eventually.of_forall fun n ↦ rfl)
    exact hdl.congr_right
      (w := (fun n : ℕ ↦ (1 : ℝ) * (n : ℝ)) / endpointLog)
      (Eventually.of_forall fun n ↦ by simp)
  have hrem : (fun n : ℕ ↦ multiplicityAbelRemainder a (n : ℝ)) =o[atTop]
      pntScale 1 := by
    have hO : multiplicityChebyshev a =O[atTop] (fun n ↦ (n : ℝ)) :=
      hweighted.isBigO
    have h := (multiplicityAbelRemainder_isLittleO ha hO).comp_tendsto
      tendsto_natCast_atTop_atTop
    rw [pntScale]
    refine h.congr (fun n ↦ rfl) (fun n ↦ ?_)
    simp only [Function.comp_apply, Pi.div_apply, one_mul, endpointLog]
  refine (hmain.add_isLittleO hrem).congr_left ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (multiplicityCount_eq_weighted_div_log_add_remainder a hn).symm

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
