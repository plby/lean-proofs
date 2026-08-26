/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

This file adapts the divisor-sum estimate from
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean`,
commit `dbc99780ae703f5a65b87da0e83ec83e5d041d9a`.
-/
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset

namespace Erdos327.Analytic

theorem invSub_antitoneOn_gt
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (c : R) :
    AntitoneOn (fun x : R ↦ (x - c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr

theorem invSub_antitoneOn_Icc
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x - c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact invSub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_pos
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    AntitoneOn (fun x : R ↦ x⁻¹) (Set.Ioi 0) := by
  convert invSub_antitoneOn_gt (R := R) 0
  ring

theorem inv_antitoneOn_Icc
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert invSub_antitoneOn_Icc a b 0 ha
  ring

theorem log_add_one_le_sum_inv (n : ℕ) :
    Real.log ↑(n + 1) ≤ ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ := by
  calc
    _ = ∫ x in (1)..↑(n + 1), x⁻¹ := ?_
    _ = ∫ x in (1 : ℕ)..↑(n + 1), x⁻¹ := ?_
    _ ≤ _ := ?_
  · rw [integral_inv (by simp [(show ¬ (1 : ℝ) ≤ 0 by norm_num)])]
    congr
    ring
  · congr
    norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc
    norm_num

theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n := by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [Icc_erase_left]
  calc
    ∑ d ∈ Ico 2 (n + 1), (d : ℝ)⁻¹ =
        ∑ d ∈ Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2)..↑(n + 1), (x - 1)⁻¹ := ?_
    _ = Real.log ↑n := ?_
  · congr
    norm_num
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply invSub_antitoneOn_Icc
    norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num
  simp [hn, show (0 : ℝ) < 1 by norm_num]

theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d : ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans 1 + Real.log (⌊y⌋₊)
  · apply sum_inv_le_log (⌊y⌋₊)
    apply le_floor
    norm_cast
  gcongr
  · norm_cast
    apply Nat.lt_of_succ_le
    apply le_floor
    norm_cast
  · apply floor_le
    linarith

/-- For divisors of a squarefree integer, the weighted harmonic divisor sum
is bounded by the corresponding power of `1 + log x`. -/
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow
    {P k : ℕ} (x : ℝ) (hx : 1 ≤ x) (hP : Squarefree P) :
    (∑ d ∈ P.divisors,
        if d ≤ x then (k : ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ)) ≤
      (1 + Real.log x) ^ k := by
  have hx_pos : 0 < x := by linarith
  calc
    _ = ∑ d ∈ P.divisors,
          ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then
              if ↑d ≤ x then (d : ℝ)⁻¹ else 0
            else 0 := ?_
    _ = ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then
            if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0
          else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k,
          ∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by
      rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
      rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_
  · apply sum_congr rfl
    intro d hd
    rw [mem_divisors] at hd
    simp_rw [ite_and]
    rw [← sum_filter, Finset.sum_const,
      ← finMulAntidiag_eq_piFinset_divisors_filter hd.1 hd.2,
      card_finMulAntidiag_of_squarefree <| hP.squarefree_of_dvd hd.1,
      if_pos hd.1]
    simp only [div_eq_mul_inv, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]
    apply sum_congr rfl
    intro a _
    rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl)
      · rw [Iff.comm, iff_and_self]
        exact fun _ => rfl
      · intro
        rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum
    intro a _
    by_cases h : ∏ i, a i ∣ P
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs
    · apply prod_nonneg
      intro i _
      norm_num
    · rfl
  · apply sum_le_sum
    intro a ha
    split_ifs with h
    · gcongr with i hi
      rw [if_pos]
      apply le_trans _ h
      norm_cast
      rw [← prod_erase_mul (a := i) (h := hi)]
      apply Nat.le_mul_of_pos_left
      rw [Fintype.mem_piFinset] at ha
      apply prod_pos
      intro j _
      exact pos_of_mem_divisors (ha j)
    · apply prod_nonneg
      intro j _
      split_ifs
      · norm_num
      · rfl
  · rw [← sum_filter]
    gcongr
    trans ∑ d ∈ Icc 1 (floor x), (d : ℝ)⁻¹
    · apply sum_le_sum_of_subset_of_nonneg
      · intro d
        rw [mem_filter, mem_Icc]
        intro hd
        constructor
        · rw [Nat.succ_le_iff]
          exact pos_of_mem_divisors hd.1
        · rw [le_floor_iff hx_pos.le]
          exact hd.2
      · norm_num
    apply sum_inv_le_log_real
    linarith

/-- A quantitative bound for the divisor weights which occur in the
Bonferroni--CRT lattice error. -/
theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow
    {P h : ℕ} (x : ℝ) (hx : 1 ≤ x) (hP : Squarefree P) :
    (∑ d ∈ P.divisors,
        if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤
      x * (1 + Real.log x) ^ h := by
  trans ∑ d ∈ P.divisors,
    x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ)
  · simp_rw [mul_ite, mul_zero, ← sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i : ℝ)⁻¹, ← mul_assoc]
    trans 1 * (h : ℝ) ^ ω i
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [← div_eq_mul_inv]
    apply one_le_div (by
      norm_cast
      exact Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [← mul_sum]
  gcongr
  exact sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP

end Erdos327.Analytic
