import ErdosProblems.Erdos381.Core
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

namespace Erdos381

open Polynomial Filter Asymptotics

noncomputable def padePoly (m : ℕ) : ℤ[X] :=
  (X - C 1) ^ (2 * m) *
    (C 3 * X - C 2) ^ (2 * m) *
      (C 3 * X - C 4) ^ (2 * m)

noncomputable def padeLowQuotient (m : ℕ) : ℤ[X] :=
  (C 4 * X - C 1) ^ (2 * m) *
    (C 6 * X - C 1) ^ (2 * m) *
      (C 3 * X - C 1) ^ (2 * m)

lemma padePoly_scale_four (m : ℕ) :
    (padePoly m).comp (C 4 * X) =
      C (4 ^ (3 * m) : ℤ) * padeLowQuotient m := by
  simp only [padePoly, padeLowQuotient, mul_comp, sub_comp, pow_comp,
    X_comp, C_comp]
  push_cast
  rw [show (C 3 * (C 4 * X) - C 2 : ℤ[X]) =
      C 2 * (C 6 * X - C 1) by norm_num; ring]
  rw [show (C 3 * (C 4 * X) - C 4 : ℤ[X]) =
      C 4 * (C 3 * X - C 1) by norm_num; ring]
  rw [mul_pow, mul_pow]
  simp only [C_pow]
  have hscalar : (4 : ℤ) ^ (3 * m) =
      2 ^ (2 * m) * 4 ^ (2 * m) := by
    calc
      (4 : ℤ) ^ (3 * m) = 4 ^ (m + 2 * m) := by congr 1 <;> omega
      _ = 4 ^ m * 4 ^ (2 * m) := by rw [pow_add]
      _ = 2 ^ (2 * m) * 4 ^ (2 * m) := by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hscalarC : (C 4 : ℤ[X]) ^ (3 * m) =
      C (2 : ℤ) ^ (2 * m) * C (4 : ℤ) ^ (2 * m) := by
    simpa only [C_pow, C_mul] using congrArg C hscalar
  rw [hscalarC]
  ring

lemma padePoly_low_coeff_dvd (m r : ℕ) (hr : r ≤ 3 * m) :
    (4 : ℤ) ^ (3 * m - r) ∣ (padePoly m).coeff r := by
  have hcoeff := congrArg (fun p : ℤ[X] ↦ p.coeff r) (padePoly_scale_four m)
  rw [comp_C_mul_X_coeff, coeff_C_mul] at hcoeff
  refine ⟨(padeLowQuotient m).coeff r, ?_⟩
  have hmul : (padePoly m).coeff r * 4 ^ r =
      (4 ^ (3 * m - r) * (padeLowQuotient m).coeff r) * 4 ^ r := by
    calc
      (padePoly m).coeff r * 4 ^ r =
          4 ^ (3 * m) * (padeLowQuotient m).coeff r := hcoeff
      _ = (4 ^ (3 * m - r) * (padeLowQuotient m).coeff r) * 4 ^ r := by
        have hp : (4 : ℤ) ^ (3 * m) = 4 ^ (3 * m - r) * 4 ^ r := by
          rw [← pow_add, Nat.sub_add_cancel hr]
        rw [hp]
        ring
  exact mul_right_cancel₀
    (pow_ne_zero r (by norm_num : (4 : ℤ) ≠ 0)) hmul

lemma natDegree_padeLinear_three_two :
    (C 3 * X - C 2 : ℤ[X]).natDegree = 1 := by
  simpa [sub_eq_add_neg] using
    (natDegree_linear (R := ℤ) (a := 3) (b := -2) (by norm_num))

lemma natDegree_padeLinear_three_four :
    (C 3 * X - C 4 : ℤ[X]).natDegree = 1 := by
  simpa [sub_eq_add_neg] using
    (natDegree_linear (R := ℤ) (a := 3) (b := -4) (by norm_num))

lemma padePoly_natDegree (m : ℕ) : (padePoly m).natDegree = 6 * m := by
  have hA : (X - C 1 : ℤ[X]) ≠ 0 := X_sub_C_ne_zero 1
  have hB : (C 3 * X - C 2 : ℤ[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : ℤ[X] ↦ p.coeff 1) h
    norm_num at this
  have hC : (C 3 * X - C 4 : ℤ[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : ℤ[X] ↦ p.coeff 1) h
    norm_num at this
  simp only [padePoly]
  rw [natDegree_mul (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB))
      (pow_ne_zero _ hC),
    natDegree_mul (pow_ne_zero _ hA) (pow_ne_zero _ hB)]
  rw [natDegree_pow' (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hA)),
    natDegree_pow' (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hB)),
    natDegree_pow' (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hC)),
    natDegree_X_sub_C, natDegree_padeLinear_three_two,
    natDegree_padeLinear_three_four]
  omega

lemma reverse_pow_int (p : ℤ[X]) (n : ℕ) :
    (p ^ n).reverse = p.reverse ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      simpa only [C_1] using (reverse_C (R := ℤ) (1 : ℤ))
  | succ n ih => rw [pow_succ, reverse_mul_of_domain, ih, pow_succ]

lemma reverse_padeLinear_one :
    (X - C 1 : ℤ[X]).reverse = C 1 - X := by
  rw [reverse, natDegree_X_sub_C]
  simp [reflect_sub]

lemma reverse_padeLinear_three_two :
    (C 3 * X - C 2 : ℤ[X]).reverse = C 3 - C 2 * X := by
  rw [reverse, natDegree_padeLinear_three_two]
  rw [reflect_sub]
  rw [show (C 3 * X : ℤ[X]) = C 3 * X ^ 1 by simp]
  rw [reflect_C_mul_X_pow]
  rw [reflect_C]
  rw [revAt_le (by omega : 1 ≤ 1)]
  norm_num

lemma reverse_padeLinear_three_four :
    (C 3 * X - C 4 : ℤ[X]).reverse = C 3 - C 4 * X := by
  rw [reverse, natDegree_padeLinear_three_four]
  rw [reflect_sub]
  rw [show (C 3 * X : ℤ[X]) = C 3 * X ^ 1 by simp]
  rw [reflect_C_mul_X_pow]
  rw [reflect_C]
  rw [revAt_le (by omega : 1 ≤ 1)]
  norm_num

lemma padePoly_reverse (m : ℕ) :
    (padePoly m).reverse =
      (C 1 - X) ^ (2 * m) *
        (C 3 - C 2 * X) ^ (2 * m) *
          (C 3 - C 4 * X) ^ (2 * m) := by
  simp only [padePoly, reverse_mul_of_domain, reverse_pow_int,
    reverse_padeLinear_one, reverse_padeLinear_three_two,
    reverse_padeLinear_three_four]

noncomputable def padeHighQuotient (m : ℕ) : ℤ[X] :=
  (C 1 - C 3 * X) ^ (2 * m) *
    (C 1 - C 2 * X) ^ (2 * m) *
      (C 1 - C 4 * X) ^ (2 * m)

lemma padePoly_reverse_scale_three (m : ℕ) :
    (padePoly m).reverse.comp (C 3 * X) =
      C (3 ^ (4 * m) : ℤ) * padeHighQuotient m := by
  rw [padePoly_reverse]
  simp only [padeHighQuotient, mul_comp, sub_comp, pow_comp, C_comp, X_comp]
  rw [show (C 3 - C 2 * (C 3 * X) : ℤ[X]) =
      C 3 * (C 1 - C 2 * X) by norm_num; ring]
  rw [show (C 3 - C 4 * (C 3 * X) : ℤ[X]) =
      C 3 * (C 1 - C 4 * X) by norm_num; ring]
  rw [mul_pow, mul_pow]
  simp only [C_pow]
  have hscalar : (3 : ℤ) ^ (4 * m) =
      3 ^ (2 * m) * 3 ^ (2 * m) := by
    rw [show 4 * m = 2 * m + 2 * m by omega, pow_add]
  have hscalarC : (C 3 : ℤ[X]) ^ (4 * m) =
      C (3 : ℤ) ^ (2 * m) * C (3 : ℤ) ^ (2 * m) := by
    simpa only [C_pow, C_mul] using congrArg C hscalar
  rw [hscalarC]
  ring

lemma padePoly_high_coeff_dvd (m r : ℕ) (hr : 3 * m ≤ r)
    (hrtop : r ≤ 6 * m) :
    (3 : ℤ) ^ (r - 3 * m) ∣ (padePoly m).coeff r := by
  have hrs : 6 * m - r ≤ 4 * m := by omega
  have hcoeff := congrArg (fun p : ℤ[X] ↦ p.coeff (6 * m - r))
    (padePoly_reverse_scale_three m)
  rw [comp_C_mul_X_coeff, coeff_C_mul] at hcoeff
  rw [coeff_reverse, padePoly_natDegree] at hcoeff
  simp only [revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hrtop] at hcoeff
  have hmul : (padePoly m).coeff r * 3 ^ (6 * m - r) =
      (3 ^ (r - 2 * m) * (padeHighQuotient m).coeff (6 * m - r)) *
        3 ^ (6 * m - r) := by
    calc
      (padePoly m).coeff r * 3 ^ (6 * m - r) =
          3 ^ (4 * m) * (padeHighQuotient m).coeff (6 * m - r) := hcoeff
      _ = (3 ^ (r - 2 * m) * (padeHighQuotient m).coeff (6 * m - r)) *
          3 ^ (6 * m - r) := by
        have hp : (3 : ℤ) ^ (4 * m) =
            3 ^ (r - 2 * m) * 3 ^ (6 * m - r) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hp]
        ring
  have hstrong : (3 : ℤ) ^ (r - 2 * m) ∣ (padePoly m).coeff r := by
    refine ⟨(padeHighQuotient m).coeff (6 * m - r), ?_⟩
    exact mul_right_cancel₀
      (pow_ne_zero (6 * m - r) (by norm_num : (3 : ℤ) ≠ 0)) hmul
  exact dvd_trans (⟨3 ^ m, by rw [← pow_add]; congr 1 <;> omega⟩) hstrong

noncomputable def padeKernelMinus (t : ℝ) : ℝ :=
  3 * t ^ 2 * (1 - t ^ 2) ^ 2 / (3 - t) ^ 3

noncomputable def padeKernelPlus (t : ℝ) : ℝ :=
  3 * t ^ 2 * (1 - t ^ 2) ^ 2 / (3 + t) ^ 3

lemma padeKernelMinus_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ padeKernelMinus t := by
  dsimp [padeKernelMinus]
  have hnum : 0 ≤ 3 * t ^ 2 * (1 - t ^ 2) ^ 2 := by positivity
  have hden : 0 ≤ (3 - t) ^ 3 := (pow_pos (by linarith) _).le
  exact div_nonneg hnum hden

lemma padeKernelPlus_nonneg {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ padeKernelPlus t := by
  dsimp [padeKernelPlus]
  positivity

lemma padeMinusPolynomial_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (3 - t) ^ 3 - 90 * t ^ 2 * (1 - t ^ 2) ^ 2 := by
  by_cases hhalf : t ≤ 1 / 2
  · let x := 2 * t
    have hx0 : 0 ≤ x := by dsimp [x]; linarith
    have hx1 : x ≤ 1 := by dsimp [x]; linarith
    have hs : 0 ≤
        27 * (1 - x) ^ 6 +
        (297 / 2) * x * (1 - x) ^ 5 +
        (1269 / 4) * x ^ 2 * (1 - x) ^ 4 +
        (2591 / 8) * x ^ 3 * (1 - x) ^ 3 +
        (1275 / 8) * x ^ 4 * (1 - x) ^ 2 +
        (285 / 8) * x ^ 5 * (1 - x) +
        (95 / 32) * x ^ 6 := by positivity
    have hid : (3 - t) ^ 3 - 90 * t ^ 2 * (1 - t ^ 2) ^ 2 =
        27 * (1 - x) ^ 6 +
        (297 / 2) * x * (1 - x) ^ 5 +
        (1269 / 4) * x ^ 2 * (1 - x) ^ 4 +
        (2591 / 8) * x ^ 3 * (1 - x) ^ 3 +
        (1275 / 8) * x ^ 4 * (1 - x) ^ 2 +
        (285 / 8) * x ^ 5 * (1 - x) +
        (95 / 32) * x ^ 6 := by
      dsimp [x]
      ring
    rwa [hid]
  · have hhalf' : 1 / 2 ≤ t := by linarith
    by_cases htwo : t ≤ 2 / 3
    · let x := 6 * t - 3
      have hx0 : 0 ≤ x := by dsimp [x]; linarith
      have hx1 : x ≤ 1 := by dsimp [x]; linarith
      have hs : 0 ≤
          (95 / 32) * (1 - x) ^ 6 +
          (95 / 8) * x * (1 - x) ^ 5 +
          (425 / 24) * x ^ 2 * (1 - x) ^ 4 +
          (2609 / 216) * x ^ 3 * (1 - x) ^ 3 +
          (49 / 12) * x ^ 4 * (1 - x) ^ 2 +
          (7 / 6) * x ^ 5 * (1 - x) +
          (29 / 81) * x ^ 6 := by positivity
      have hid : (3 - t) ^ 3 - 90 * t ^ 2 * (1 - t ^ 2) ^ 2 =
          (95 / 32) * (1 - x) ^ 6 +
          (95 / 8) * x * (1 - x) ^ 5 +
          (425 / 24) * x ^ 2 * (1 - x) ^ 4 +
          (2609 / 216) * x ^ 3 * (1 - x) ^ 3 +
          (49 / 12) * x ^ 4 * (1 - x) ^ 2 +
          (7 / 6) * x ^ 5 * (1 - x) +
          (29 / 81) * x ^ 6 := by
        dsimp [x]
        ring
      rwa [hid]
    · have htwo' : 2 / 3 ≤ t := by linarith
      let x := 3 * t - 2
      have hx0 : 0 ≤ x := by dsimp [x]; linarith
      have hx1 : x ≤ 1 := by dsimp [x]; linarith
      have hs : 0 ≤
          (29 / 81) * (1 - x) ^ 6 +
          (37 / 9) * x * (1 - x) ^ 5 +
          (89 / 3) * x ^ 2 * (1 - x) ^ 4 +
          (2233 / 27) * x ^ 3 * (1 - x) ^ 3 +
          (302 / 3) * x ^ 4 * (1 - x) ^ 2 +
          52 * x ^ 5 * (1 - x) +
          8 * x ^ 6 := by positivity
      have hid : (3 - t) ^ 3 - 90 * t ^ 2 * (1 - t ^ 2) ^ 2 =
          (29 / 81) * (1 - x) ^ 6 +
          (37 / 9) * x * (1 - x) ^ 5 +
          (89 / 3) * x ^ 2 * (1 - x) ^ 4 +
          (2233 / 27) * x ^ 3 * (1 - x) ^ 3 +
          (302 / 3) * x ^ 4 * (1 - x) ^ 2 +
          52 * x ^ 5 * (1 - x) +
          8 * x ^ 6 := by
        dsimp [x]
        ring
      rwa [hid]

lemma padeKernelMinus_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    padeKernelMinus t ≤ 1 / 30 := by
  have hden : 0 < (3 - t) ^ 3 := pow_pos (by linarith) _
  rw [padeKernelMinus, div_le_iff₀ hden]
  nlinarith [padeMinusPolynomial_nonneg ht0 ht1]

lemma padePlusNumerator_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    27 * (t ^ 2 * (1 - t ^ 2) ^ 2) ≤ 4 := by
  have hs0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hs1 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - t)]
  have hfour : 0 ≤ 4 - 3 * t ^ 2 := by linarith
  have hfac : 0 ≤ (4 - 3 * t ^ 2) * (3 * t ^ 2 - 1) ^ 2 := by positivity
  nlinarith [hfac]

lemma padeKernelPlus_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    padeKernelPlus t ≤ 1 / 60 := by
  have hdenpos : 0 < (3 + t) ^ 3 := pow_pos (by linarith) _
  have hquad : 0 ≤ t ^ 2 + 9 * t + 27 := by nlinarith [sq_nonneg t]
  have hden : 27 ≤ (3 + t) ^ 3 := by
    calc
      27 ≤ 27 + t * (t ^ 2 + 9 * t + 27) := by
        linarith [mul_nonneg ht0 hquad]
      _ = (3 + t) ^ 3 := by ring
  rw [padeKernelPlus, div_le_iff₀ hdenpos]
  nlinarith [padePlusNumerator_le ht0 ht1]

lemma padeMinusLowerPolynomial_nonneg {t : ℝ}
    (ht0 : 3 / 5 ≤ t) (ht1 : t ≤ 7 / 10) :
    0 ≤ 96 * t ^ 2 * (1 - t ^ 2) ^ 2 - (3 - t) ^ 3 := by
  let x := 10 * t - 6
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  have hs : 0 ≤
      (5184 / 15625) * (1 - x) ^ 6 +
      (48888 / 15625) * x * (1 - x) ^ 5 +
      (28983 / 3125) * x ^ 2 * (1 - x) ^ 4 +
      (310009 / 25000) * x ^ 3 * (1 - x) ^ 3 +
      (197451 / 25000) * x ^ 4 * (1 - x) ^ 2 +
      (255399 / 125000) * x ^ 5 * (1 - x) +
      (8513 / 125000) * x ^ 6 := by positivity
  have hid : 96 * t ^ 2 * (1 - t ^ 2) ^ 2 - (3 - t) ^ 3 =
      (5184 / 15625) * (1 - x) ^ 6 +
      (48888 / 15625) * x * (1 - x) ^ 5 +
      (28983 / 3125) * x ^ 2 * (1 - x) ^ 4 +
      (310009 / 25000) * x ^ 3 * (1 - x) ^ 3 +
      (197451 / 25000) * x ^ 4 * (1 - x) ^ 2 +
      (255399 / 125000) * x ^ 5 * (1 - x) +
      (8513 / 125000) * x ^ 6 := by
    dsimp [x]
    ring
  rwa [hid]

lemma one_div_32_le_padeKernelMinus {t : ℝ}
    (ht0 : 3 / 5 ≤ t) (ht1 : t ≤ 7 / 10) :
    1 / 32 ≤ padeKernelMinus t := by
  have hden : 0 < (3 - t) ^ 3 := pow_pos (by linarith) _
  rw [padeKernelMinus, le_div_iff₀ hden]
  nlinarith [padeMinusLowerPolynomial_nonneg ht0 ht1]

noncomputable def padeBase (z : ℝ) : ℝ :=
  (z - 1) ^ 2 * (3 * z - 2) ^ 2 * (3 * z - 4) ^ 2 / z ^ 3

noncomputable def padeIntegrand (m : ℕ) (z : ℝ) : ℝ :=
  padeBase z ^ m / z

lemma padeBase_eq_kernelMinus {z : ℝ} (hz : z ≠ 0) :
    padeBase z = padeKernelMinus (3 - 3 * z) := by
  rw [padeBase, padeKernelMinus]
  field_simp [hz]
  ring

lemma padeBase_eq_kernelPlus {z : ℝ} (hz : z ≠ 0) :
    padeBase z = padeKernelPlus (3 * z - 3) := by
  rw [padeBase, padeKernelPlus]
  field_simp [hz]
  ring

lemma padeIntegrand_nonneg {m : ℕ} {z : ℝ} (hz : 0 < z) :
    0 ≤ padeIntegrand m z := by
  dsimp [padeIntegrand, padeBase]
  positivity

lemma padeIntegrand_intervalIntegrable (m : ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (padeIntegrand m) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro z hz
  have hzpos : 0 < z := by
    exact (lt_min ha hb).trans_le hz.1
  apply ContinuousAt.continuousWithinAt
  unfold padeIntegrand padeBase
  have hz0 : z ≠ 0 := hzpos.ne'
  fun_prop (disch := aesop)

noncomputable def padeMinusIntegral (m : ℕ) : ℝ :=
  ∫ z in (2 / 3 : ℝ)..1, padeIntegrand m z

noncomputable def padePlusIntegral (m : ℕ) : ℝ :=
  ∫ z in (1 : ℝ)..(4 / 3), padeIntegrand m z

lemma padeMinusIntegral_nonneg (m : ℕ) : 0 ≤ padeMinusIntegral m := by
  rw [padeMinusIntegral]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro z hz
  exact padeIntegrand_nonneg (by linarith [hz.1])

lemma padePlusIntegral_nonneg (m : ℕ) : 0 ≤ padePlusIntegral m := by
  rw [padePlusIntegral]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro z hz
  exact padeIntegrand_nonneg (by linarith [hz.1])

lemma padeIntegrand_minus_le (m : ℕ) {z : ℝ}
    (hz0 : 2 / 3 ≤ z) (hz1 : z ≤ 1) :
    padeIntegrand m z ≤ (3 / 2) * (1 / 30) ^ m := by
  have hzpos : 0 < z := by linarith
  let t := 3 - 3 * z
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hb0 : 0 ≤ padeBase z := by
    rw [padeBase_eq_kernelMinus hzpos.ne']
    exact padeKernelMinus_nonneg ht0 ht1
  have hb : padeBase z ≤ 1 / 30 := by
    rw [padeBase_eq_kernelMinus hzpos.ne']
    exact padeKernelMinus_le ht0 ht1
  have hpow : padeBase z ^ m ≤ (1 / 30) ^ m :=
    pow_le_pow_left₀ hb0 hb m
  have hinv : z⁻¹ ≤ 3 / 2 := by
    have h : 1 / z ≤ 3 / 2 := by
      rw [div_le_iff₀ hzpos]
      nlinarith
    simpa only [one_div] using h
  rw [padeIntegrand, div_eq_mul_inv]
  calc
    padeBase z ^ m * z⁻¹ ≤ (1 / 30) ^ m * z⁻¹ := by gcongr
    _ ≤ (1 / 30) ^ m * (3 / 2) := by gcongr
    _ = (3 / 2) * (1 / 30) ^ m := by ring

lemma padeIntegrand_plus_le (m : ℕ) {z : ℝ}
    (hz0 : 1 ≤ z) (hz1 : z ≤ 4 / 3) :
    padeIntegrand m z ≤ (1 / 60) ^ m := by
  have hzpos : 0 < z := by linarith
  let t := 3 * z - 3
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hb0 : 0 ≤ padeBase z := by
    rw [padeBase_eq_kernelPlus hzpos.ne']
    exact padeKernelPlus_nonneg ht0
  have hb : padeBase z ≤ 1 / 60 := by
    rw [padeBase_eq_kernelPlus hzpos.ne']
    exact padeKernelPlus_le ht0 ht1
  have hpow : padeBase z ^ m ≤ (1 / 60) ^ m :=
    pow_le_pow_left₀ hb0 hb m
  have hinv : z⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hzpos]
    exact hz0
  rw [padeIntegrand, div_eq_mul_inv]
  calc
    padeBase z ^ m * z⁻¹ ≤ (1 / 60) ^ m * z⁻¹ := by gcongr
    _ ≤ (1 / 60) ^ m * 1 := by gcongr
    _ = (1 / 60) ^ m := mul_one _

lemma padeMinusIntegral_le (m : ℕ) :
    padeMinusIntegral m ≤ (1 / 30) ^ m := by
  have hmono := intervalIntegral.integral_mono_on
    (show (2 / 3 : ℝ) ≤ 1 by norm_num)
    (padeIntegrand_intervalIntegrable m (by norm_num) (by norm_num))
    intervalIntegrable_const
    (fun z hz ↦ padeIntegrand_minus_le m hz.1 hz.2)
  rw [intervalIntegral.integral_const] at hmono
  rw [padeMinusIntegral]
  have hp : 0 ≤ (1 / 30 : ℝ) ^ m := by positivity
  norm_num [smul_eq_mul] at hmono
  nlinarith

lemma padePlusIntegral_le (m : ℕ) :
    padePlusIntegral m ≤ (1 / 60) ^ m := by
  have hmono := intervalIntegral.integral_mono_on
    (show (1 : ℝ) ≤ 4 / 3 by norm_num)
    (padeIntegrand_intervalIntegrable m (by norm_num) (by norm_num))
    intervalIntegrable_const
    (fun z hz ↦ padeIntegrand_plus_le m hz.1 hz.2)
  rw [intervalIntegral.integral_const] at hmono
  rw [padePlusIntegral]
  have hp : 0 ≤ (1 / 60 : ℝ) ^ m := by positivity
  norm_num [smul_eq_mul] at hmono
  nlinarith

lemma padeIntegrand_lower (m : ℕ) {z : ℝ}
    (hz0 : 23 / 30 ≤ z) (hz1 : z ≤ 4 / 5) :
    (1 / 32) ^ m ≤ padeIntegrand m z := by
  have hzpos : 0 < z := by linarith
  let t := 3 - 3 * z
  have ht0 : 3 / 5 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 7 / 10 := by dsimp [t]; linarith
  have hb : 1 / 32 ≤ padeBase z := by
    rw [padeBase_eq_kernelMinus hzpos.ne']
    exact one_div_32_le_padeKernelMinus ht0 ht1
  have hpow : (1 / 32) ^ m ≤ padeBase z ^ m := by
    exact pow_le_pow_left₀ (by norm_num) hb m
  have honeinv : 1 ≤ z⁻¹ := by
    have hzle : z ≤ 1 := hz1.trans (by norm_num)
    have h : 1 ≤ 1 / z := by
      rw [le_div_iff₀ hzpos]
      simpa using hzle
    simpa only [one_div] using h
  rw [padeIntegrand, div_eq_mul_inv]
  calc
    (1 / 32) ^ m ≤ (1 / 32) ^ m * z⁻¹ := by
      nth_rewrite 1 [← mul_one ((1 / 32) ^ m)]
      gcongr
    _ ≤ padeBase z ^ m * z⁻¹ := by gcongr

lemma padeMinusIntegral_lower (m : ℕ) :
    (1 / 30) * (1 / 32) ^ m ≤ padeMinusIntegral m := by
  have hsub : (1 / 30) * (1 / 32) ^ m ≤
      ∫ z in (23 / 30 : ℝ)..(4 / 5), padeIntegrand m z := by
    have hmono := intervalIntegral.integral_mono_on
      (show (23 / 30 : ℝ) ≤ 4 / 5 by norm_num)
      intervalIntegrable_const
      (padeIntegrand_intervalIntegrable m (by norm_num) (by norm_num))
      (fun z hz ↦ padeIntegrand_lower m hz.1 hz.2)
    rw [intervalIntegral.integral_const] at hmono
    convert hmono using 1 <;> ring
  apply hsub.trans
  rw [padeMinusIntegral]
  apply intervalIntegral.integral_mono_interval
  · norm_num
  · norm_num
  · norm_num
  · change ∀ᵐ z ∂MeasureTheory.volume.restrict (Set.Ioc (2 / 3 : ℝ) 1),
        0 ≤ padeIntegrand m z
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun z hz ↦
      padeIntegrand_nonneg (by linarith [hz.1])
  · exact padeIntegrand_intervalIntegrable m (by norm_num) (by norm_num)

noncomputable def padeLaurentTerm (m r : ℕ) (z : ℝ) : ℝ :=
  ((padePoly m).coeff r : ℝ) * z ^ ((r : ℤ) - (3 * m : ℕ) - 1)

lemma natPow_div_natPow_eq_zpow {z : ℝ} (hz : z ≠ 0) (r n : ℕ) :
    z ^ r / z ^ (n + 1) = z ^ ((r : ℤ) - (n : ℤ) - 1) := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hz]
  congr 1
  push_cast
  ring

lemma padePoly_eval_real (m : ℕ) (z : ℝ) :
    (padePoly m).eval₂ (Int.castRingHom ℝ) z =
      (z - 1) ^ (2 * m) * (3 * z - 2) ^ (2 * m) *
        (3 * z - 4) ^ (2 * m) := by
  simp only [padePoly, eval₂_mul, eval₂_pow, eval₂_sub, eval₂_X, eval₂_C,
    eval₂_ofNat]
  norm_num

lemma padeIntegrand_eq_laurentSum (m : ℕ) {z : ℝ} (hz : z ≠ 0) :
    padeIntegrand m z =
      ∑ r ∈ Finset.range (6 * m + 1), padeLaurentTerm m r z := by
  rw [padeIntegrand, padeBase]
  have hnum :
      ((z - 1) ^ 2 * (3 * z - 2) ^ 2 * (3 * z - 4) ^ 2) ^ m =
        (padePoly m).eval₂ (Int.castRingHom ℝ) z := by
    rw [padePoly_eval_real]
    repeat' rw [mul_pow]
    repeat' rw [pow_mul]
  rw [div_pow, div_div, ← pow_mul, ← pow_succ,
    hnum, Polynomial.eval₂_eq_sum_range, padePoly_natDegree]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  rw [padeLaurentTerm]
  change ((padePoly m).coeff r : ℝ) * z ^ r / z ^ (3 * m + 1) =
    ((padePoly m).coeff r : ℝ) * z ^ ((r : ℤ) - (3 * m : ℕ) - 1)
  rw [mul_div_assoc]
  congr 1
  exact natPow_div_natPow_eq_zpow hz r (3 * m)

lemma padeLaurentTerm_intervalIntegrable (m r : ℕ) {a : ℝ} (ha : 0 < a) :
    IntervalIntegrable (padeLaurentTerm m r) MeasureTheory.volume 1 a := by
  apply ContinuousOn.intervalIntegrable
  intro z hz
  have hzpos : 0 < z := (lt_min (by norm_num : (0 : ℝ) < 1) ha).trans_le hz.1
  apply ContinuousAt.continuousWithinAt
  unfold padeLaurentTerm
  have hz0 : z ≠ 0 := hzpos.ne'
  fun_prop (disch := aesop)

lemma integral_padeLaurentTerm (m r : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ z in (1 : ℝ)..a, padeLaurentTerm m r z) =
      if r = 3 * m then
        ((padePoly m).coeff r : ℝ) * Real.log a
      else
        ((padePoly m).coeff r : ℝ) *
          (a ^ ((r : ℤ) - (3 * m : ℕ)) - 1) /
            (((r : ℤ) - (3 * m : ℕ) : ℤ) : ℝ) := by
  unfold padeLaurentTerm
  rw [intervalIntegral.integral_const_mul]
  by_cases hr : r = 3 * m
  · rw [if_pos hr]
    subst r
    have hexp : ((3 * m : ℕ) : ℤ) - (3 * m : ℕ) - 1 = -1 := by omega
    rw [hexp]
    congr 1
    simpa only [zpow_neg_one, div_one] using
      (integral_inv_of_pos (a := (1 : ℝ)) (b := a) (by norm_num) ha)
  · rw [if_neg hr]
    have hexp : (r : ℤ) - (3 * m : ℕ) - 1 ≠ -1 := by
      push_cast
      omega
    have hzero : (0 : ℝ) ∉ Set.uIcc 1 a := by
      simp only [Set.mem_uIcc, Set.mem_Icc]
      push_neg
      constructor <;> intro h <;> linarith
    rw [integral_zpow (Or.inr ⟨hexp, hzero⟩)]
    have hk : ((r : ℤ) - (3 * m : ℕ) - 1) + 1 =
        (r : ℤ) - (3 * m : ℕ) := by ring
    have hkR :
        ((((r : ℤ) - (3 * m : ℕ) - 1 : ℤ) : ℝ) + 1) =
          (((r : ℤ) - (3 * m : ℕ) : ℤ) : ℝ) := by
      exact_mod_cast hk
    rw [hk, one_zpow]
    rw [hkR]
    ring

noncomputable def padeRemainderReal (m : ℕ) (a : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (6 * m + 1),
    if r = 3 * m then 0 else
      ((padePoly m).coeff r : ℝ) *
        (a ^ ((r : ℤ) - (3 * m : ℕ)) - 1) /
          (((r : ℤ) - (3 * m : ℕ) : ℤ) : ℝ)

lemma padeIntegral_eq_log_add_remainder (m : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ z in (1 : ℝ)..a, padeIntegrand m z) =
      ((padePoly m).coeff (3 * m) : ℝ) * Real.log a +
        padeRemainderReal m a := by
  calc
    (∫ z in (1 : ℝ)..a, padeIntegrand m z) =
        ∫ z in (1 : ℝ)..a,
          ∑ r ∈ Finset.range (6 * m + 1), padeLaurentTerm m r z := by
      apply intervalIntegral.integral_congr
      intro z hz
      exact padeIntegrand_eq_laurentSum m
        ((lt_min (by norm_num : (0 : ℝ) < 1) ha).trans_le hz.1).ne'
    _ = ∑ r ∈ Finset.range (6 * m + 1),
          ∫ z in (1 : ℝ)..a, padeLaurentTerm m r z := by
      apply intervalIntegral.integral_finset_sum
      intro r hr
      exact padeLaurentTerm_intervalIntegrable m r ha
    _ = ∑ r ∈ Finset.range (6 * m + 1),
          if r = 3 * m then
            ((padePoly m).coeff r : ℝ) * Real.log a
          else
            ((padePoly m).coeff r : ℝ) *
              (a ^ ((r : ℤ) - (3 * m : ℕ)) - 1) /
                (((r : ℤ) - (3 * m : ℕ) : ℤ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact integral_padeLaurentTerm m r ha
    _ = ((padePoly m).coeff (3 * m) : ℝ) * Real.log a +
        padeRemainderReal m a := by
      rw [padeRemainderReal]
      have hmem : 3 * m ∈ Finset.range (6 * m + 1) := by simp; omega
      have hcentral :
          ((padePoly m).coeff (3 * m) : ℝ) * Real.log a =
            ∑ r ∈ Finset.range (6 * m + 1),
              if r = 3 * m then
                ((padePoly m).coeff (3 * m) : ℝ) * Real.log a
              else 0 := by
        symm
        simp [Finset.sum_ite_eq', hmem]
      rw [hcentral, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : r = 3 * m
      · subst r
        simp [hmem]
      · simp [h]

noncomputable def padeLcm (m : ℕ) : ℕ := Nat.lcmUpto (3 * m)

lemma padeLcm_pos (m : ℕ) : 0 < padeLcm m := by
  exact Nat.lcmUpto_pos _

lemma dvd_padeLcm {m k : ℕ} (hk0 : 0 < k) (hk : k ≤ 3 * m) :
    k ∣ padeLcm m := by
  rw [padeLcm, Nat.lcmUpto]
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hk0, hk⟩)

lemma two_thirds_zpow_neg_nat (k : ℕ) :
    (2 / 3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ k / 2 ^ k := by
  rw [zpow_neg, zpow_natCast, div_pow]
  field_simp

lemma four_thirds_zpow_neg_nat (k : ℕ) :
    (4 / 3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ k / 4 ^ k := by
  rw [zpow_neg, zpow_natCast, div_pow]
  field_simp

lemma two_thirds_zpow_nat (k : ℕ) :
    (2 / 3 : ℝ) ^ (k : ℤ) = (2 : ℝ) ^ k / 3 ^ k := by
  rw [zpow_natCast, div_pow]

lemma four_thirds_zpow_nat (k : ℕ) :
    (4 / 3 : ℝ) ^ (k : ℤ) = (4 : ℝ) ^ k / 3 ^ k := by
  rw [zpow_natCast, div_pow]

noncomputable def padeRemainderTermReal (m r : ℕ) (a : ℝ) : ℝ :=
  if r = 3 * m then 0 else
    ((padePoly m).coeff r : ℝ) *
      (a ^ ((r : ℤ) - (3 * m : ℕ)) - 1) /
        (((r : ℤ) - (3 * m : ℕ) : ℤ) : ℝ)

lemma padeRemainderReal_eq_sum_terms (m : ℕ) (a : ℝ) :
    padeRemainderReal m a =
      ∑ r ∈ Finset.range (6 * m + 1), padeRemainderTermReal m r a := by
  rfl

lemma scaled_two_thirds_remainder_term_isInt (m r : ℕ)
    (hr : r < 6 * m + 1) :
    ∃ q : ℤ, (q : ℝ) =
      (padeLcm m : ℝ) * padeRemainderTermReal m r (2 / 3) := by
  by_cases hcentral : r = 3 * m
  · refine ⟨0, ?_⟩
    simp [padeRemainderTermReal, hcentral]
  by_cases hlow : r < 3 * m
  · let k := 3 * m - r
    have hk0 : 0 < k := by dsimp [k]; omega
    have hk : k ≤ 3 * m := by dsimp [k]; omega
    obtain ⟨d, hd⟩ := dvd_padeLcm hk0 hk
    have hc4 := padePoly_low_coeff_dvd m r (by omega)
    have hc2pow4 : (2 : ℤ) ^ k ∣ 4 ^ k := by
      refine ⟨2 ^ k, ?_⟩
      rw [show (4 : ℤ) = 2 * 2 by norm_num, mul_pow]
    obtain ⟨c, hc⟩ := dvd_trans hc2pow4 hc4
    refine ⟨(d : ℤ) * c * ((2 : ℤ) ^ k - 3 ^ k), ?_⟩
    have he : (r : ℤ) - (3 * m : ℕ) = -(k : ℤ) := by
      dsimp [k]
      push_cast
      omega
    have hdR : (padeLcm m : ℝ) = (k : ℝ) * d := by exact_mod_cast hd
    have hcR : ((padePoly m).coeff r : ℝ) = (2 : ℝ) ^ k * c := by
      exact_mod_cast hc
    rw [padeRemainderTermReal, if_neg hcentral, he,
      two_thirds_zpow_neg_nat, hdR, hcR]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    have htwo : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    field_simp
    ring
  · have hhigh : 3 * m < r := by omega
    let k := r - 3 * m
    have hk0 : 0 < k := by dsimp [k]; omega
    have hk : k ≤ 3 * m := by dsimp [k]; omega
    obtain ⟨d, hd⟩ := dvd_padeLcm hk0 hk
    have hc3 := padePoly_high_coeff_dvd m r (by omega) (by omega)
    obtain ⟨c, hc⟩ := hc3
    refine ⟨(d : ℤ) * c * ((2 : ℤ) ^ k - 3 ^ k), ?_⟩
    have he : (r : ℤ) - (3 * m : ℕ) = (k : ℤ) := by
      dsimp [k]
      push_cast
      omega
    have hdR : (padeLcm m : ℝ) = (k : ℝ) * d := by exact_mod_cast hd
    have hcR : ((padePoly m).coeff r : ℝ) = (3 : ℝ) ^ k * c := by
      exact_mod_cast hc
    rw [padeRemainderTermReal, if_neg hcentral, he,
      two_thirds_zpow_nat, hdR, hcR]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hthree : (3 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    field_simp

lemma scaled_four_thirds_remainder_term_isInt (m r : ℕ)
    (hr : r < 6 * m + 1) :
    ∃ q : ℤ, (q : ℝ) =
      (padeLcm m : ℝ) * padeRemainderTermReal m r (4 / 3) := by
  by_cases hcentral : r = 3 * m
  · refine ⟨0, ?_⟩
    simp [padeRemainderTermReal, hcentral]
  by_cases hlow : r < 3 * m
  · let k := 3 * m - r
    have hk0 : 0 < k := by dsimp [k]; omega
    have hk : k ≤ 3 * m := by dsimp [k]; omega
    obtain ⟨d, hd⟩ := dvd_padeLcm hk0 hk
    obtain ⟨c, hc⟩ := padePoly_low_coeff_dvd m r (by omega)
    refine ⟨(d : ℤ) * c * ((4 : ℤ) ^ k - 3 ^ k), ?_⟩
    have he : (r : ℤ) - (3 * m : ℕ) = -(k : ℤ) := by
      dsimp [k]
      push_cast
      omega
    have hdR : (padeLcm m : ℝ) = (k : ℝ) * d := by exact_mod_cast hd
    have hcR : ((padePoly m).coeff r : ℝ) = (4 : ℝ) ^ k * c := by
      exact_mod_cast hc
    rw [padeRemainderTermReal, if_neg hcentral, he,
      four_thirds_zpow_neg_nat, hdR, hcR]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hfour : (4 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    field_simp
    ring
  · have hhigh : 3 * m < r := by omega
    let k := r - 3 * m
    have hk0 : 0 < k := by dsimp [k]; omega
    have hk : k ≤ 3 * m := by dsimp [k]; omega
    obtain ⟨d, hd⟩ := dvd_padeLcm hk0 hk
    obtain ⟨c, hc⟩ := padePoly_high_coeff_dvd m r (by omega) (by omega)
    refine ⟨(d : ℤ) * c * ((4 : ℤ) ^ k - 3 ^ k), ?_⟩
    have he : (r : ℤ) - (3 * m : ℕ) = (k : ℤ) := by
      dsimp [k]
      push_cast
      omega
    have hdR : (padeLcm m : ℝ) = (k : ℝ) * d := by exact_mod_cast hd
    have hcR : ((padePoly m).coeff r : ℝ) = (3 : ℝ) ^ k * c := by
      exact_mod_cast hc
    rw [padeRemainderTermReal, if_neg hcentral, he,
      four_thirds_zpow_nat, hdR, hcR]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hthree : (3 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    field_simp

lemma scaled_two_thirds_remainder_isInt (m : ℕ) :
    ∃ q : ℤ, (q : ℝ) =
      (padeLcm m : ℝ) * padeRemainderReal m (2 / 3) := by
  classical
  let q : ℕ → ℤ := fun r ↦
    if hr : r ∈ Finset.range (6 * m + 1) then
      Classical.choose (scaled_two_thirds_remainder_term_isInt m r
        (Finset.mem_range.mp hr))
    else 0
  have hq (r : ℕ) (hr : r ∈ Finset.range (6 * m + 1)) :
      (q r : ℝ) = (padeLcm m : ℝ) *
        padeRemainderTermReal m r (2 / 3) := by
    simp only [q, dif_pos hr]
    exact Classical.choose_spec (scaled_two_thirds_remainder_term_isInt m r
      (Finset.mem_range.mp hr))
  refine ⟨∑ r ∈ Finset.range (6 * m + 1), q r, ?_⟩
  push_cast
  rw [padeRemainderReal_eq_sum_terms, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact hq r hr

lemma scaled_four_thirds_remainder_isInt (m : ℕ) :
    ∃ q : ℤ, (q : ℝ) =
      (padeLcm m : ℝ) * padeRemainderReal m (4 / 3) := by
  classical
  let q : ℕ → ℤ := fun r ↦
    if hr : r ∈ Finset.range (6 * m + 1) then
      Classical.choose (scaled_four_thirds_remainder_term_isInt m r
        (Finset.mem_range.mp hr))
    else 0
  have hq (r : ℕ) (hr : r ∈ Finset.range (6 * m + 1)) :
      (q r : ℝ) = (padeLcm m : ℝ) *
        padeRemainderTermReal m r (4 / 3) := by
    simp only [q, dif_pos hr]
    exact Classical.choose_spec (scaled_four_thirds_remainder_term_isInt m r
      (Finset.mem_range.mp hr))
  refine ⟨∑ r ∈ Finset.range (6 * m + 1), q r, ?_⟩
  push_cast
  rw [padeRemainderReal_eq_sum_terms, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact hq r hr

lemma eventually_psi_le_log_three_mul :
    ∀ᶠ x : ℝ in atTop,
      Chebyshev.psi x ≤ Real.log 3 * x := by
  have hlog3 : 1 < Real.log (3 : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three
  have herr := WeakPNT''.isLittleO.def (sub_pos.mpr hlog3)
  filter_upwards [herr, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hx0] at hx
  calc
    Chebyshev.psi x ≤ x + |Chebyshev.psi x - x| := by
      linarith [le_abs_self (Chebyshev.psi x - x)]
    _ ≤ x + (Real.log 3 - 1) * x := by gcongr
    _ = Real.log 3 * x := by ring

lemma eventually_padeLcm_le_twentyseven_pow :
    ∀ᶠ m : ℕ in atTop, padeLcm m ≤ 27 ^ m := by
  have ht : Tendsto (fun m : ℕ ↦ (3 : ℝ) * (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hpsi := eventually_psi_le_log_three_mul.filter_mono ht
  filter_upwards [hpsi] with m hm
  have hreal : (padeLcm m : ℝ) ≤ ((27 : ℕ) ^ m : ℝ) := by
    rw [← Real.log_le_log_iff
      (by exact_mod_cast padeLcm_pos m : (0 : ℝ) < padeLcm m)
      (by positivity : (0 : ℝ) < (27 : ℕ) ^ m)]
    calc
      Real.log (padeLcm m : ℝ) = Chebyshev.psi (3 * m) := by
        symm
        simpa [padeLcm] using Chebyshev.psi_eq_log_lcmUpto (3 * m)
      _ ≤ Real.log 3 * ((3 : ℝ) * (m : ℝ)) := by simpa using hm
      _ = Real.log ((27 : ℕ) ^ m : ℝ) := by
        have hlog27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
          calc
            Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ 3) := by norm_num
            _ = 3 * Real.log 3 := by rw [Real.log_pow]; norm_num
        push_cast
        rw [Real.log_pow, hlog27]
        ring
  exact_mod_cast hreal

lemma natAbs_coeff_X_sub_C_pow_le (b m k : ℕ) (hb : 0 < b) :
    Int.natAbs (((X - C (b : ℤ)) ^ (2 * m)).coeff k) ≤
      (2 * b) ^ (2 * m) := by
  rw [show (X - C (b : ℤ) : ℤ[X]) = X + C (-(b : ℤ)) by simp [sub_eq_add_neg],
    coeff_X_add_C_pow]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg,
    Int.natAbs_natCast]
  calc
    b ^ (2 * m - k) * (2 * m).choose k ≤
        b ^ (2 * m) * 2 ^ (2 * m) :=
      Nat.mul_le_mul
        (Nat.pow_le_pow_right hb (Nat.sub_le (2 * m) k))
        (Nat.choose_le_two_pow (2 * m) k)
    _ = (2 * b) ^ (2 * m) := by rw [mul_pow]; ac_rfl

lemma natAbs_coeff_scaled_X_sub_C_pow_le
    (a b m k : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Int.natAbs (((C (a : ℤ) * X - C (b : ℤ)) ^ (2 * m)).coeff k) ≤
      (2 * b * a) ^ (2 * m) := by
  have hpoly : (C (a : ℤ) * X - C (b : ℤ) : ℤ[X]) =
      (X - C (b : ℤ)).comp (C (a : ℤ) * X) := by simp
  rw [hpoly, ← pow_comp, comp_C_mul_X_coeff, Int.natAbs_mul,
    Int.natAbs_pow, Int.natAbs_natCast]
  by_cases hk : k ≤ 2 * m
  · calc
      Int.natAbs (((X - C (b : ℤ)) ^ (2 * m)).coeff k) * a ^ k ≤
          (2 * b) ^ (2 * m) * a ^ (2 * m) :=
        Nat.mul_le_mul (natAbs_coeff_X_sub_C_pow_le b m k hb)
          (Nat.pow_le_pow_right ha hk)
      _ = (2 * b * a) ^ (2 * m) := by simp only [mul_pow]
  · have hk' : 2 * m < k := by omega
    rw [show (X - C (b : ℤ) : ℤ[X]) = X + C (-(b : ℤ)) by
          simp [sub_eq_add_neg],
      coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt hk']
    simp

lemma natAbs_coeff_mul_le (p q : ℤ[X]) (n A B : ℕ)
    (hp : ∀ k, Int.natAbs (p.coeff k) ≤ A)
    (hq : ∀ k, Int.natAbs (q.coeff k) ≤ B) :
    Int.natAbs ((p * q).coeff n) ≤ (n + 1) * A * B := by
  rw [coeff_mul]
  calc
    Int.natAbs (∑ x ∈ Finset.antidiagonal n,
        p.coeff x.1 * q.coeff x.2) ≤
        ∑ x ∈ Finset.antidiagonal n,
          Int.natAbs (p.coeff x.1 * q.coeff x.2) :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _x ∈ Finset.antidiagonal n, A * B := by
      gcongr with x hx
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hp x.1) (hq x.2)
    _ = (n + 1) * A * B := by simp [mul_assoc]

lemma three_mul_add_one_le_four_pow (m : ℕ) : 3 * m + 1 ≤ 4 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      calc
        3 * (m + 1) + 1 ≤ 4 * (3 * m + 1) := by omega
        _ ≤ 4 * 4 ^ m := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (m + 1) := by rw [pow_succ']

lemma padePoly_coeff_natAbs_le (m k : ℕ) (hk : k ≤ 3 * m) :
    Int.natAbs ((padePoly m).coeff k) ≤ 5308416 ^ m := by
  let p : ℤ[X] := (X - C 1) ^ (2 * m)
  let q : ℤ[X] := (C 3 * X - C 2) ^ (2 * m)
  let r : ℤ[X] := (C 3 * X - C 4) ^ (2 * m)
  have hp (i : ℕ) : Int.natAbs (p.coeff i) ≤ 4 ^ m := by
    dsimp [p]
    convert natAbs_coeff_X_sub_C_pow_le 1 m i (by norm_num) using 1 <;>
      norm_num [pow_mul]
  have hq (i : ℕ) : Int.natAbs (q.coeff i) ≤ 144 ^ m := by
    dsimp [q]
    convert natAbs_coeff_scaled_X_sub_C_pow_le 3 2 m i (by norm_num) (by norm_num)
      using 1 <;> norm_num [pow_mul]
  have hr (i : ℕ) : Int.natAbs (r.coeff i) ≤ 576 ^ m := by
    dsimp [r]
    convert natAbs_coeff_scaled_X_sub_C_pow_le 3 4 m i (by norm_num) (by norm_num)
      using 1 <;> norm_num [pow_mul]
  have hpq (i : ℕ) (hi : i ≤ 3 * m) :
      Int.natAbs ((p * q).coeff i) ≤ (3 * m + 1) * 4 ^ m * 144 ^ m := by
    exact (natAbs_coeff_mul_le p q i (4 ^ m) (144 ^ m) hp hq).trans (by gcongr)
  have hmain : Int.natAbs (((p * q) * r).coeff k) ≤
      (3 * m + 1) * ((3 * m + 1) * 4 ^ m * 144 ^ m) * 576 ^ m := by
    rw [coeff_mul]
    calc
      Int.natAbs (∑ x ∈ Finset.antidiagonal k,
          (p * q).coeff x.1 * r.coeff x.2) ≤
          ∑ x ∈ Finset.antidiagonal k,
            Int.natAbs ((p * q).coeff x.1 * r.coeff x.2) :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ _x ∈ Finset.antidiagonal k,
          ((3 * m + 1) * 4 ^ m * 144 ^ m) * 576 ^ m := by
        gcongr with x hx
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (hpq x.1 (by
          have := Finset.mem_antidiagonal.mp hx
          omega)) (hr x.2)
      _ = (k + 1) * ((3 * m + 1) * 4 ^ m * 144 ^ m) * 576 ^ m := by
        simp [mul_assoc]
      _ ≤ (3 * m + 1) * ((3 * m + 1) * 4 ^ m * 144 ^ m) * 576 ^ m := by
        gcongr
  rw [show padePoly m = (p * q) * r by rfl]
  apply hmain.trans
  have hsquare : (3 * m + 1) ^ 2 ≤ 16 ^ m := by
    calc
      (3 * m + 1) ^ 2 ≤ (4 ^ m) ^ 2 :=
        Nat.pow_le_pow_left (three_mul_add_one_le_four_pow m) 2
      _ = 16 ^ m := by rw [pow_two, ← mul_pow]; norm_num
  calc
    (3 * m + 1) * ((3 * m + 1) * 4 ^ m * 144 ^ m) * 576 ^ m =
        (3 * m + 1) ^ 2 * (4 * 144 * 576) ^ m := by
      rw [mul_pow, mul_pow]
      ring
    _ ≤ 16 ^ m * (4 * 144 * 576) ^ m := by gcongr
    _ = 5308416 ^ m := by rw [← mul_pow]; norm_num

noncomputable def padeTwoThirdsInteger (m : ℕ) : ℤ :=
  Classical.choose (scaled_two_thirds_remainder_isInt m)

lemma padeTwoThirdsInteger_spec (m : ℕ) :
    (padeTwoThirdsInteger m : ℝ) =
      (padeLcm m : ℝ) * padeRemainderReal m (2 / 3) :=
  Classical.choose_spec (scaled_two_thirds_remainder_isInt m)

noncomputable def padeFourThirdsInteger (m : ℕ) : ℤ :=
  Classical.choose (scaled_four_thirds_remainder_isInt m)

lemma padeFourThirdsInteger_spec (m : ℕ) :
    (padeFourThirdsInteger m : ℝ) =
      (padeLcm m : ℝ) * padeRemainderReal m (4 / 3) :=
  Classical.choose_spec (scaled_four_thirds_remainder_isInt m)

noncomputable def padeLogCoefficient (m : ℕ) : ℤ :=
  (padeLcm m : ℤ) * (padePoly m).coeff (3 * m)

noncomputable def padeNumeratorP (m : ℕ) : ℤ := padeTwoThirdsInteger m

noncomputable def padeDenominatorQ (m : ℕ) : ℤ :=
  padeTwoThirdsInteger m - padeFourThirdsInteger m

lemma log_two_thirds_eq_neg_log_three_halves :
    Real.log (2 / 3 : ℝ) = -Real.log (3 / 2 : ℝ) := by
  have h : (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ := by norm_num
  rw [h, Real.log_inv]

lemma log_three_halves_add_log_four_thirds :
    Real.log (3 / 2 : ℝ) + Real.log (4 / 3 : ℝ) = Real.log 2 := by
  rw [Real.log_div, Real.log_div] <;> norm_num
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [hlog4]
  ring

lemma pade_three_halves_linear_form (m : ℕ) :
    (padeLogCoefficient m : ℝ) * Real.log (3 / 2) -
        (padeNumeratorP m : ℝ) =
      (padeLcm m : ℝ) * padeMinusIntegral m := by
  have hI := padeIntegral_eq_log_add_remainder m
    (a := (2 / 3 : ℝ)) (by norm_num)
  have hI' : -padeMinusIntegral m =
      ((padePoly m).coeff (3 * m) : ℝ) * Real.log (2 / 3) +
        padeRemainderReal m (2 / 3) := by
    calc
      -padeMinusIntegral m =
          ∫ z in (1 : ℝ)..(2 / 3), padeIntegrand m z := by
        rw [padeMinusIntegral, intervalIntegral.integral_symm]
        simp
      _ = _ := hI
  rw [log_two_thirds_eq_neg_log_three_halves] at hI'
  have hform :
      ((padePoly m).coeff (3 * m) : ℝ) * Real.log (3 / 2) -
          padeRemainderReal m (2 / 3) = padeMinusIntegral m := by
    linarith
  rw [padeNumeratorP, padeTwoThirdsInteger_spec, padeLogCoefficient]
  push_cast
  calc
    (padeLcm m : ℝ) * ((padePoly m).coeff (3 * m) : ℝ) *
          Real.log (3 / 2) -
        (padeLcm m : ℝ) * padeRemainderReal m (2 / 3) =
        (padeLcm m : ℝ) *
          (((padePoly m).coeff (3 * m) : ℝ) * Real.log (3 / 2) -
            padeRemainderReal m (2 / 3)) := by ring
    _ = (padeLcm m : ℝ) * padeMinusIntegral m := by rw [hform]

lemma pade_four_thirds_linear_form (m : ℕ) :
    (padeLogCoefficient m : ℝ) * Real.log (4 / 3) +
        (padeFourThirdsInteger m : ℝ) =
      (padeLcm m : ℝ) * padePlusIntegral m := by
  have hI := padeIntegral_eq_log_add_remainder m
    (a := (4 / 3 : ℝ)) (by norm_num)
  have hI' : padePlusIntegral m =
      ((padePoly m).coeff (3 * m) : ℝ) * Real.log (4 / 3) +
        padeRemainderReal m (4 / 3) := by
    simpa [padePlusIntegral] using hI
  rw [padeFourThirdsInteger_spec, padeLogCoefficient]
  push_cast
  calc
    (padeLcm m : ℝ) * ((padePoly m).coeff (3 * m) : ℝ) *
          Real.log (4 / 3) +
        (padeLcm m : ℝ) * padeRemainderReal m (4 / 3) =
        (padeLcm m : ℝ) *
          (((padePoly m).coeff (3 * m) : ℝ) * Real.log (4 / 3) +
            padeRemainderReal m (4 / 3)) := by ring
    _ = (padeLcm m : ℝ) * padePlusIntegral m := by rw [← hI']

lemma pade_log_two_linear_form (m : ℕ) :
    (padeLogCoefficient m : ℝ) * Real.log 2 -
        (padeDenominatorQ m : ℝ) =
      (padeLcm m : ℝ) * (padeMinusIntegral m + padePlusIntegral m) := by
  have hminus := pade_three_halves_linear_form m
  have hplus := pade_four_thirds_linear_form m
  rw [padeNumeratorP] at hminus
  rw [padeDenominatorQ]
  push_cast
  rw [← log_three_halves_add_log_four_thirds]
  linear_combination hminus + hplus

lemma nicolasTheta_le_two_thirds : nicolasTheta ≤ 2 / 3 := by
  have hlogs : 3 * Real.log 3 < 5 * Real.log 2 := by
    have hlogmono : Real.log (27 : ℝ) < Real.log 32 :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    have hlog27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
      calc
        Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ 3) := by norm_num
        _ = 3 * Real.log 3 := by rw [Real.log_pow]; norm_num
    have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
      calc
        Real.log (32 : ℝ) = Real.log ((2 : ℝ) ^ 5) := by norm_num
        _ = 5 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rwa [hlog27, hlog32] at hlogmono
  have halpha : 3 * Real.log (3 / 2 : ℝ) < 2 * Real.log 2 := by
    rw [Real.log_div] <;> norm_num
    linarith
  rw [nicolasTheta, div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  linarith

lemma padePlusIntegral_le_quarter_minus (m : ℕ) (hm : 8 ≤ m) :
    padePlusIntegral m ≤ padeMinusIntegral m / 4 := by
  have hratio : (8 / 15 : ℝ) ^ m ≤ 1 / 120 := by
    calc
      (8 / 15 : ℝ) ^ m ≤ (8 / 15 : ℝ) ^ 8 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ ≤ 1 / 120 := by norm_num
  calc
    padePlusIntegral m ≤ (1 / 60 : ℝ) ^ m := padePlusIntegral_le m
    _ = (1 / 32 : ℝ) ^ m * (8 / 15 : ℝ) ^ m := by
      rw [← mul_pow]
      norm_num
    _ ≤ (1 / 32 : ℝ) ^ m * (1 / 120) := by gcongr
    _ = (1 / 4) * ((1 / 30) * (1 / 32 : ℝ) ^ m) := by ring
    _ ≤ (1 / 4) * padeMinusIntegral m := by
      gcongr
      exact padeMinusIntegral_lower m
    _ = padeMinusIntegral m / 4 := by ring

noncomputable def padeThetaError (m : ℕ) : ℝ :=
  (padeDenominatorQ m : ℝ) * nicolasTheta - (padeNumeratorP m : ℝ)

lemma log_two_mul_nicolasTheta :
    Real.log 2 * nicolasTheta = Real.log (3 / 2) := by
  rw [nicolasTheta]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

lemma padeThetaError_eq (m : ℕ) :
    padeThetaError m = (padeLcm m : ℝ) *
      ((1 - nicolasTheta) * padeMinusIntegral m -
        nicolasTheta * padePlusIntegral m) := by
  have hminus := pade_three_halves_linear_form m
  have htwo := pade_log_two_linear_form m
  rw [← log_two_mul_nicolasTheta] at hminus
  rw [padeThetaError]
  linear_combination hminus - nicolasTheta * htwo

lemma padeThetaError_upper (m : ℕ) (hL : padeLcm m ≤ 27 ^ m) :
    |padeThetaError m| ≤ 2 * (9 / 10 : ℝ) ^ m := by
  have htheta0 : 0 ≤ nicolasTheta := nicolasTheta_pos.le
  have htheta1 : nicolasTheta ≤ 1 := nicolasTheta_lt_one.le
  have hminus0 := padeMinusIntegral_nonneg m
  have hplus0 := padePlusIntegral_nonneg m
  have hinside :
      |(1 - nicolasTheta) * padeMinusIntegral m -
          nicolasTheta * padePlusIntegral m| ≤
        padeMinusIntegral m + padePlusIntegral m := by
    calc
      |(1 - nicolasTheta) * padeMinusIntegral m -
          nicolasTheta * padePlusIntegral m| ≤
          |(1 - nicolasTheta) * padeMinusIntegral m| +
            |nicolasTheta * padePlusIntegral m| := abs_sub _ _
      _ = (1 - nicolasTheta) * padeMinusIntegral m +
          nicolasTheta * padePlusIntegral m := by
        rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr htheta1) hminus0),
          abs_of_nonneg (mul_nonneg htheta0 hplus0)]
      _ ≤ padeMinusIntegral m + padePlusIntegral m := by
        nlinarith [mul_nonneg nicolasTheta_pos.le hminus0,
          mul_nonneg (sub_nonneg.mpr htheta1) hplus0]
  rw [padeThetaError_eq, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ padeLcm m)]
  calc
    (padeLcm m : ℝ) *
        |(1 - nicolasTheta) * padeMinusIntegral m -
          nicolasTheta * padePlusIntegral m| ≤
        (padeLcm m : ℝ) * (padeMinusIntegral m + padePlusIntegral m) := by
      gcongr
    _ ≤ (27 : ℝ) ^ m * ((1 / 30 : ℝ) ^ m + (1 / 60 : ℝ) ^ m) := by
      gcongr
      · exact_mod_cast hL
      · exact padeMinusIntegral_le m
      · exact padePlusIntegral_le m
    _ = (9 / 10 : ℝ) ^ m + (9 / 20 : ℝ) ^ m := by
      rw [mul_add, ← mul_pow, ← mul_pow]
      norm_num
    _ ≤ 2 * (9 / 10 : ℝ) ^ m := by
      have hpow : (9 / 20 : ℝ) ^ m ≤ (9 / 10 : ℝ) ^ m := by gcongr <;> norm_num
      linarith

lemma padeThetaError_lower (m : ℕ) (hm : 8 ≤ m) :
    (1 / 180) * (1 / 32 : ℝ) ^ m ≤ padeThetaError m := by
  have htheta0 : 0 ≤ nicolasTheta := nicolasTheta_pos.le
  have htheta : nicolasTheta ≤ 2 / 3 := nicolasTheta_le_two_thirds
  have hminus0 := padeMinusIntegral_nonneg m
  have hplus0 := padePlusIntegral_nonneg m
  have hplusQuarter := padePlusIntegral_le_quarter_minus m hm
  have hinside : (1 / 6) * padeMinusIntegral m ≤
      (1 - nicolasTheta) * padeMinusIntegral m -
        nicolasTheta * padePlusIntegral m := by
    have hθplus : nicolasTheta * padePlusIntegral m ≤
        (2 / 3) * (padeMinusIntegral m / 4) := by
      exact mul_le_mul htheta hplusQuarter hplus0 (by norm_num)
    nlinarith
  rw [padeThetaError_eq]
  calc
    (1 / 180) * (1 / 32 : ℝ) ^ m =
        (1 / 6) * ((1 / 30) * (1 / 32 : ℝ) ^ m) := by ring
    _ ≤ (1 / 6) * padeMinusIntegral m := by
      gcongr
      exact padeMinusIntegral_lower m
    _ ≤ (padeLcm m : ℝ) * ((1 / 6) * padeMinusIntegral m) := by
      have hLone : (1 : ℝ) ≤ padeLcm m := by
        exact_mod_cast (padeLcm_pos m)
      nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6) hminus0]
    _ ≤ (padeLcm m : ℝ) *
        ((1 - nicolasTheta) * padeMinusIntegral m -
          nicolasTheta * padePlusIntegral m) := by gcongr

lemma padeDenominatorQ_abs_le (m : ℕ) (hm : 1 ≤ m)
    (hL : padeLcm m ≤ 27 ^ m) :
    |(padeDenominatorQ m : ℝ)| ≤ (429981696 : ℝ) ^ m := by
  have hc : |(((padePoly m).coeff (3 * m) : ℤ) : ℝ)| ≤
      (5308416 : ℝ) ^ m := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast padePoly_coeff_natAbs_le m (3 * m) (by omega)
  have hB : |(padeLogCoefficient m : ℝ)| ≤
      (27 * 5308416 : ℝ) ^ m := by
    rw [padeLogCoefficient]
    push_cast
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ padeLcm m)]
    calc
      (padeLcm m : ℝ) *
          |(((padePoly m).coeff (3 * m) : ℤ) : ℝ)| ≤
          (27 : ℝ) ^ m * (5308416 : ℝ) ^ m := by
        gcongr
        exact_mod_cast hL
      _ = (27 * 5308416 : ℝ) ^ m := by rw [mul_pow]
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlog2one : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_one_gt_two.le
  have hsum0 : 0 ≤ padeMinusIntegral m + padePlusIntegral m :=
    add_nonneg (padeMinusIntegral_nonneg m) (padePlusIntegral_nonneg m)
  have hsum : (padeLcm m : ℝ) *
      (padeMinusIntegral m + padePlusIntegral m) ≤ 2 := by
    calc
      (padeLcm m : ℝ) *
          (padeMinusIntegral m + padePlusIntegral m) ≤
          (27 : ℝ) ^ m *
            ((1 / 30 : ℝ) ^ m + (1 / 60 : ℝ) ^ m) := by
        gcongr
        · exact_mod_cast hL
        · exact padeMinusIntegral_le m
        · exact padePlusIntegral_le m
      _ = (9 / 10 : ℝ) ^ m + (9 / 20 : ℝ) ^ m := by
        rw [mul_add, ← mul_pow, ← mul_pow]
        norm_num
      _ ≤ 2 := by
        have h1 : (9 / 10 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have h2 : (9 / 20 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
  have hqeq : (padeDenominatorQ m : ℝ) =
      (padeLogCoefficient m : ℝ) * Real.log 2 -
        (padeLcm m : ℝ) *
          (padeMinusIntegral m + padePlusIntegral m) := by
    linarith [pade_log_two_linear_form m]
  rw [hqeq]
  calc
    |(padeLogCoefficient m : ℝ) * Real.log 2 -
        (padeLcm m : ℝ) *
          (padeMinusIntegral m + padePlusIntegral m)| ≤
        |(padeLogCoefficient m : ℝ) * Real.log 2| +
          |(padeLcm m : ℝ) *
            (padeMinusIntegral m + padePlusIntegral m)| := abs_sub _ _
    _ = |(padeLogCoefficient m : ℝ)| * Real.log 2 +
        (padeLcm m : ℝ) *
          (padeMinusIntegral m + padePlusIntegral m) := by
      rw [abs_mul, abs_of_nonneg hlog2,
        abs_of_nonneg (mul_nonneg (by positivity) hsum0)]
    _ ≤ (27 * 5308416 : ℝ) ^ m + 2 := by
      nlinarith [mul_le_mul hB hlog2one hlog2
        (by positivity : (0 : ℝ) ≤ (27 * 5308416 : ℝ) ^ m)]
    _ ≤ 3 * (27 * 5308416 : ℝ) ^ m := by
      have hone : (1 : ℝ) ≤ (27 * 5308416 : ℝ) ^ m :=
        one_le_pow₀ (by norm_num)
      linarith
    _ ≤ (429981696 : ℝ) ^ m := by
      have hthree : (3 : ℝ) ≤ 3 ^ m := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hm)
      calc
        3 * (27 * 5308416 : ℝ) ^ m ≤
            3 ^ m * (27 * 5308416 : ℝ) ^ m := by gcongr
        _ = (429981696 : ℝ) ^ m := by rw [← mul_pow]; norm_num

lemma scaled_pade_decay_lt_half (v m : ℕ) (hv : 0 < v)
    (hm : 32 * (Nat.log 2 v + 1) ≤ m) :
    (v : ℝ) * (2 * (9 / 10 : ℝ) ^ m) < 1 / 2 := by
  let s := Nat.log 2 v
  have hvpowNat : v < 2 ^ (s + 1) := by
    exact Nat.lt_pow_succ_log_self (by norm_num) v
  have hvpow : (v : ℝ) < (2 : ℝ) ^ (s + 1) := by exact_mod_cast hvpowNat
  have hdecay : (9 / 10 : ℝ) ^ m ≤ (9 / 10 : ℝ) ^ (32 * (s + 1)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hbase : 2 * (9 / 10 : ℝ) ^ 32 ≤ 1 / 4 := by norm_num
  have hquarter : (1 / 4 : ℝ) ^ (s + 1) ≤ 1 / 4 := by
    simpa only [pow_one] using
      (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) ≤ 1) (by omega : 1 ≤ s + 1))
  calc
    (v : ℝ) * (2 * (9 / 10 : ℝ) ^ m) ≤
        (v : ℝ) * (2 * (9 / 10 : ℝ) ^ (32 * (s + 1))) := by gcongr
    _ < (2 : ℝ) ^ (s + 1) *
        (2 * (9 / 10 : ℝ) ^ (32 * (s + 1))) := by
      gcongr
    _ = 2 * (2 * (9 / 10 : ℝ) ^ 32) ^ (s + 1) := by
      rw [pow_mul]
      calc
        (2 : ℝ) ^ (s + 1) *
            (2 * ((9 / 10 : ℝ) ^ 32) ^ (s + 1)) =
            2 * ((2 : ℝ) ^ (s + 1) *
              ((9 / 10 : ℝ) ^ 32) ^ (s + 1)) := by ring
        _ = 2 * (2 * (9 / 10 : ℝ) ^ 32) ^ (s + 1) := by
          rw [mul_pow]
    _ ≤ 2 * (1 / 4 : ℝ) ^ (s + 1) := by gcongr
    _ ≤ 1 / 2 := by linarith

lemma pade_separation (u : ℤ) (v m : ℕ) (hv : 0 < v)
    (hm8 : 8 ≤ m) (hmDecay : 32 * (Nat.log 2 v + 1) ≤ m)
    (hL : padeLcm m ≤ 27 ^ m) :
    ((1 / 180) * (1 / 32 : ℝ) ^ m) / (429981696 : ℝ) ^ m ≤
      |(v : ℝ) * nicolasTheta - (u : ℝ)| := by
  let q : ℤ := padeDenominatorQ m
  let p : ℤ := padeNumeratorP m
  let e : ℝ := padeThetaError m
  let t : ℝ := (v : ℝ) * nicolasTheta - (u : ℝ)
  let δ : ℝ := (1 / 180) * (1 / 32 : ℝ) ^ m
  let H : ℝ := (429981696 : ℝ) ^ m
  let D : ℤ := (v : ℤ) * p - u * q
  have heq : (q : ℝ) * t = (v : ℝ) * e + (D : ℝ) := by
    dsimp [q, p, e, t, D, padeThetaError]
    push_cast
    ring
  have hδe : δ ≤ e := by
    dsimp [δ, e]
    exact padeThetaError_lower m hm8
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hepos : 0 < e := hδpos.trans_le hδe
  have hsmall : (v : ℝ) * |e| < 1 / 2 := by
    calc
      (v : ℝ) * |e| ≤ (v : ℝ) * (2 * (9 / 10 : ℝ) ^ m) := by
        gcongr
        dsimp [e]
        exact padeThetaError_upper m hL
      _ < 1 / 2 := scaled_pade_decay_lt_half v m hv hmDecay
  have hq : |(q : ℝ)| ≤ H := by
    dsimp [q, H]
    exact padeDenominatorQ_abs_le m (by omega) hL
  have hHpos : 0 < H := by dsimp [H]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    have hp : (1 / 32 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp0 : 0 ≤ (1 / 32 : ℝ) ^ m := by positivity
    nlinarith
  have hcommon : δ ≤ H * |t| := by
    by_cases hD : D = 0
    · have habs := congrArg abs heq
      have hprod : |(q : ℝ)| * |t| = (v : ℝ) * e := by
        simpa [hD, abs_mul,
          abs_of_nonneg (by exact_mod_cast hv.le : (0 : ℝ) ≤ (v : ℝ)),
          abs_of_pos hepos] using habs
      calc
        δ ≤ e := hδe
        _ ≤ (v : ℝ) * e := by
          have hvone : (1 : ℝ) ≤ v := by exact_mod_cast hv
          nlinarith
        _ = |(q : ℝ)| * |t| := hprod.symm
        _ ≤ H * |t| := by gcongr
    · have hDabs : (1 : ℝ) ≤ |(D : ℝ)| := by
        have hDnat : 1 ≤ D.natAbs := (Int.natAbs_pos.mpr hD).nat_succ_le
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
        exact_mod_cast hDnat
      have hDexpr : (D : ℝ) = (q : ℝ) * t - (v : ℝ) * e := by
        linarith [heq]
      have hDupper : |(D : ℝ)| ≤ |(q : ℝ)| * |t| + (v : ℝ) * |e| := by
        rw [hDexpr]
        calc
          |(q : ℝ) * t - (v : ℝ) * e| ≤
              |(q : ℝ) * t| + |(v : ℝ) * e| := abs_sub _ _
          _ = |(q : ℝ)| * |t| + (v : ℝ) * |e| := by
            rw [abs_mul, abs_mul,
              abs_of_nonneg (by exact_mod_cast hv.le : (0 : ℝ) ≤ v)]
      have hhalfprod : (1 / 2 : ℝ) ≤ |(q : ℝ)| * |t| := by
        linarith
      calc
        δ ≤ 1 / 2 := hδhalf
        _ ≤ |(q : ℝ)| * |t| := hhalfprod
        _ ≤ H * |t| := by gcongr
  change δ / H ≤ |t|
  rw [div_le_iff₀ hHpos]
  simpa [mul_comm] using hcommon

def padeIrrationalityBase : ℕ := 32 * 429981696

lemma pade_index_power_bound (T v : ℕ) (hv : 0 < v) :
    padeIrrationalityBase ^ (T + 32 * (Nat.log 2 v + 1)) ≤
      padeIrrationalityBase ^ (T + 32) *
        v ^ (32 * 34) := by
  let s := Nat.log 2 v
  let A := padeIrrationalityBase
  have hA : A ≤ 2 ^ 34 := by norm_num [A, padeIrrationalityBase]
  have hs : 2 ^ s ≤ v := Nat.pow_log_le_self 2 hv.ne'
  have hsmall : A ^ (32 * s) ≤ v ^ (32 * 34) := by
    calc
      A ^ (32 * s) ≤ (2 ^ 34) ^ (32 * s) := Nat.pow_le_pow_left hA _
      _ = 2 ^ (34 * (32 * s)) := (pow_mul 2 34 (32 * s)).symm
      _ = 2 ^ (s * (32 * 34)) := by congr 1; omega
      _ = (2 ^ s) ^ (32 * 34) := by rw [pow_mul]
      _ ≤ v ^ (32 * 34) := Nat.pow_le_pow_left hs _
  change A ^ (T + 32 * (s + 1)) ≤ A ^ (T + 32) * v ^ (32 * 34)
  rw [show T + 32 * (s + 1) = (T + 32) + 32 * s by omega, pow_add]
  exact Nat.mul_le_mul_left _ hsmall

lemma pade_separation_scale_eq (m : ℕ) :
    ((1 / 180) * (1 / 32 : ℝ) ^ m) / (429981696 : ℝ) ^ m =
      1 / (180 * (padeIrrationalityBase : ℝ) ^ m) := by
  rw [padeIrrationalityBase, Nat.cast_mul, Nat.cast_ofNat, mul_pow]
  field_simp
  have hcancel : (1 / 32 : ℝ) ^ m * 32 ^ m = 1 := by
    rw [one_div_pow]
    simpa [one_div] using
      inv_mul_cancel₀ (pow_ne_zero m (by norm_num : (32 : ℝ) ≠ 0))
  calc
    (1 / 32 : ℝ) ^ m * 32 ^ m * (429981696 : ℝ) ^ m =
        1 * (429981696 : ℝ) ^ m := by rw [hcancel]
    _ = (429981696 : ℝ) ^ m := one_mul _

theorem nicolasFeldmanEstimate : NicolasFeldmanEstimate := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
    eventually_padeLcm_le_twentyseven_pow
  let T := max M 8
  let K : ℕ := 32 * 34
  let c : ℝ := 1 /
    (180 * (padeIrrationalityBase : ℝ) ^ (T + 32))
  have hbasepos : (0 : ℝ) < padeIrrationalityBase := by
    norm_num [padeIrrationalityBase]
  refine ⟨c, ?_, K, ?_⟩
  · dsimp [c]
    exact one_div_pos.mpr (mul_pos (by norm_num) (pow_pos hbasepos _))
  · intro u v hv
    let m := T + 32 * (Nat.log 2 v + 1)
    have hmT : T ≤ m := by dsimp [m]; omega
    have hmM : M ≤ m := (le_max_left M 8).trans hmT
    have hm8 : 8 ≤ m := (le_max_right M 8).trans hmT
    have hmDecay : 32 * (Nat.log 2 v + 1) ≤ m := by dsimp [m]; omega
    have hL : padeLcm m ≤ 27 ^ m := hM m hmM
    have hsep := pade_separation u v m hv hm8 hmDecay hL
    have hpowerNat : padeIrrationalityBase ^ m ≤
        padeIrrationalityBase ^ (T + 32) * v ^ K := by
      simpa [m, K] using pade_index_power_bound T v hv
    have hpower : (padeIrrationalityBase : ℝ) ^ m ≤
        (padeIrrationalityBase : ℝ) ^ (T + 32) * (v : ℝ) ^ K := by
      exact_mod_cast hpowerNat
    have hden :
        180 * (padeIrrationalityBase : ℝ) ^ m ≤
          (180 * (padeIrrationalityBase : ℝ) ^ (T + 32)) *
            (v : ℝ) ^ K := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hpower (by norm_num : (0 : ℝ) ≤ 180)
    have hdenSmallPos :
        0 < 180 * (padeIrrationalityBase : ℝ) ^ m :=
      mul_pos (by norm_num) (pow_pos hbasepos _)
    calc
      c / (v : ℝ) ^ K =
          1 / ((180 * (padeIrrationalityBase : ℝ) ^ (T + 32)) *
            (v : ℝ) ^ K) := by
        dsimp [c]
        field_simp
      _ ≤ 1 / (180 * (padeIrrationalityBase : ℝ) ^ m) :=
        one_div_le_one_div_of_le hdenSmallPos hden
      _ = ((1 / 180) * (1 / 32 : ℝ) ^ m) /
          (429981696 : ℝ) ^ m := (pade_separation_scale_eq m).symm
      _ ≤ |(v : ℝ) * nicolasTheta - (u : ℝ)| := hsep

end Erdos381
