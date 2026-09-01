/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos733.Counting
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Erdős Problem 733: an alternative dyadic product estimate

This file gives an independent assembly of the analytic estimate.  The key
point is to keep the geometric weights in the two ranges: the low-range
coordinate is bounded by a constant times `sqrt (sqrt n) * sqrt q`, while
the high-range coordinate is bounded by a constant times
`sqrt n * sqrt (sqrt n) / sqrt q`.
-/

namespace Erdos733

noncomputable section

/-- The same integral piecewise cap used in the main analytic development. -/
def dyadicAnalyticCapAlt (A n i : ℕ) : ℕ :=
  let q := dyadicScale i
  if q ^ 2 ≤ n then A * n ^ 2 / q ^ 3 else A * n / q

lemma dyadicAnalyticCapAlt_of_sq_le {A n i : ℕ}
    (h : dyadicScale i ^ 2 ≤ n) :
    dyadicAnalyticCapAlt A n i = A * n ^ 2 / dyadicScale i ^ 3 := by
  simp [dyadicAnalyticCapAlt, h]

lemma dyadicAnalyticCapAlt_of_lt_sq {A n i : ℕ}
    (h : n < dyadicScale i ^ 2) :
    dyadicAnalyticCapAlt A n i = A * n / dyadicScale i := by
  simp [dyadicAnalyticCapAlt, Nat.not_le_of_lt h]

private lemma choose_cast_le_exp_mul_log_alt (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    (N.choose k : ℝ) ≤
      Real.exp ((k : ℝ) * Real.log (Real.exp 1 * (N : ℝ) / k)) := by
  have hchoose : 0 < (N.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkN
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hN : 0 < N := hk.trans_le hkN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.log_le_iff_le_exp hchoose]
  calc
    Real.log (N.choose k : ℝ) ≤
        Real.log ((N : ℝ) ^ k / (k.factorial : ℝ)) :=
      Real.log_le_log hchoose (Nat.choose_le_pow_div k N)
    _ = (k : ℝ) * Real.log N - Real.log (k.factorial : ℝ) := by
      rw [Real.log_div (pow_ne_zero _ hNR.ne') (by positivity), Real.log_pow]
    _ ≤ (k : ℝ) * Real.log N - ((k : ℝ) * Real.log k - k) := by
      have hstirling := Stirling.le_log_factorial_stirling hk.ne'
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hpi1 : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      linarith [Real.log_nonneg hk1, Real.log_nonneg hpi1]
    _ = (k : ℝ) * Real.log (Real.exp 1 * (N : ℝ) / k) := by
      rw [Real.log_div (mul_pos (Real.exp_pos 1) hNR).ne' hkR.ne',
        Real.log_mul (Real.exp_ne_zero 1) hNR.ne', Real.log_exp]
      ring

private lemma choose_cast_le_exp_rpow_alt (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N)
    {ε : ℝ} (hε : 0 < ε) :
    (N.choose k : ℝ) ≤
      Real.exp ((k : ℝ) * ((Real.exp 1 * (N : ℝ) / k) ^ ε / ε)) := by
  refine (choose_cast_le_exp_mul_log_alt N k hk hkN).trans ?_
  apply Real.exp_le_exp.mpr
  gcongr
  exact Real.log_le_rpow_div (by positivity) hε

/-- The coordinate exponent, using `1/8` below and `1/4` above the cutoff. -/
def dyadicAnalyticExponentAlt (A n i : ℕ) : ℝ :=
  let q := dyadicScale i
  let c := dyadicAnalyticCapAlt A n i
  if c = 0 then 0
  else if q ^ 2 ≤ n then
    (q : ℝ) *
      ((Real.exp 1 * ((q + c : ℕ) : ℝ) / q) ^ (1 / 8 : ℝ) / (1 / 8 : ℝ))
  else
    (c : ℝ) *
      ((Real.exp 1 * ((q + c : ℕ) : ℝ) / c) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ))

lemma choose_dyadicAnalyticCapAlt_le_exp (A n i : ℕ) :
    (((dyadicScale i + dyadicAnalyticCapAlt A n i).choose
      (dyadicAnalyticCapAlt A n i) : ℕ) : ℝ) ≤
      Real.exp (dyadicAnalyticExponentAlt A n i) := by
  let q := dyadicScale i
  let c := dyadicAnalyticCapAlt A n i
  have hq : 0 < q := dyadicScale_pos i
  by_cases hc : c = 0
  · simp [dyadicAnalyticExponentAlt, c, hc]
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc
    by_cases hlo : q ^ 2 ≤ n
    · change (((q + c).choose c : ℕ) : ℝ) ≤
        Real.exp (dyadicAnalyticExponentAlt A n i)
      rw [← Nat.choose_symm_add]
      simpa [dyadicAnalyticExponentAlt, q, c, hc, hlo] using
        (choose_cast_le_exp_rpow_alt (q + c) q hq (Nat.le_add_right q c)
          (by norm_num : (0 : ℝ) < 1 / 8))
    · simpa [dyadicAnalyticExponentAlt, q, c, hc, hlo] using
        (choose_cast_le_exp_rpow_alt (q + c) c hcpos (Nat.le_add_left c q)
          (by norm_num : (0 : ℝ) < 1 / 4))

private lemma rpow_one_eighth_mul_sq_div_fourth_alt {K x y : ℝ}
    (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 < y) :
    (K * x ^ 2 / y ^ 4) ^ (1 / 8 : ℝ) =
      K ^ (1 / 8 : ℝ) * x ^ (1 / 4 : ℝ) / Real.sqrt y := by
  rw [Real.div_rpow (mul_nonneg hK (sq_nonneg x)) (by positivity),
    Real.mul_rpow hK (sq_nonneg x),
    ← Real.rpow_natCast_mul hx 2 (1 / 8 : ℝ),
    ← Real.rpow_natCast_mul hy.le 4 (1 / 8 : ℝ),
    Real.sqrt_eq_rpow]
  norm_num

/-- The pointwise low-range majorant used by the geometric-prefix lemma. -/
lemma dyadicAnalyticExponentAlt_le_low (A n i : ℕ)
    (hlo : dyadicScale i ^ 2 ≤ n) :
    dyadicAnalyticExponentAlt A n i ≤
      8 * (Real.exp 1 * ((A : ℝ) + 1)) ^ (1 / 8 : ℝ) *
        (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (dyadicScale i) := by
  let q := dyadicScale i
  let c := dyadicAnalyticCapAlt A n i
  have hq : 0 < q := dyadicScale_pos i
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hloR : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hlo
  by_cases hc : c = 0
  · rw [show dyadicAnalyticExponentAlt A n i = 0 by
      simp [dyadicAnalyticExponentAlt, c, hc]]
    positivity
  · have hcR : (c : ℝ) ≤ (A : ℝ) * (n : ℝ) ^ 2 / q ^ 3 := by
      rw [show c = A * n ^ 2 / q ^ 3 by
        dsimp [c, q]
        exact dyadicAnalyticCapAlt_of_sq_le hlo]
      calc
        ((A * n ^ 2 / q ^ 3 : ℕ) : ℝ) ≤
            ((A * n ^ 2 : ℕ) : ℝ) / (q ^ 3 : ℕ) := Nat.cast_div_le
        _ = (A : ℝ) * (n : ℝ) ^ 2 / q ^ 3 := by norm_num
    have hcMul : (c : ℝ) * q ^ 3 ≤ A * (n : ℝ) ^ 2 := by
      calc
        (c : ℝ) * q ^ 3 ≤
            ((A : ℝ) * n ^ 2 / q ^ 3) * q ^ 3 :=
          mul_le_mul_of_nonneg_right hcR (by positivity)
        _ = A * n ^ 2 := by field_simp
    have hq4 : (q : ℝ) ^ 4 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hsum : ((q : ℝ) + c) * q ^ 3 ≤
        ((A : ℝ) + 1) * n ^ 2 := by nlinarith
    have hratio : (((q + c : ℕ) : ℝ) / q) ≤
        ((A : ℝ) + 1) * n ^ 2 / q ^ 4 := by
      rw [div_le_div_iff₀ hqR (pow_pos hqR 4)]
      have ht := mul_le_mul_of_nonneg_right hsum hqR.le
      norm_num at ht ⊢
      nlinarith
    have hbase : Real.exp 1 * (((q + c : ℕ) : ℝ) / q) ≤
        Real.exp 1 * (((A : ℝ) + 1) * n ^ 2 / q ^ 4) :=
      mul_le_mul_of_nonneg_left hratio (Real.exp_pos 1).le
    have hrpow := Real.rpow_le_rpow (by positivity) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [show dyadicAnalyticExponentAlt A n i =
        (q : ℝ) *
          ((Real.exp 1 * (((q + c : ℕ) : ℝ) / q)) ^ (1 / 8 : ℝ) /
            (1 / 8 : ℝ)) by
      simp only [dyadicAnalyticExponentAlt, q, c, hc, if_false, hlo, if_true]
      field_simp]
    calc
      (q : ℝ) *
          ((Real.exp 1 * (((q + c : ℕ) : ℝ) / q)) ^ (1 / 8 : ℝ) /
            (1 / 8 : ℝ)) ≤
          q * ((Real.exp 1 * (((A : ℝ) + 1) * n ^ 2 / q ^ 4)) ^
            (1 / 8 : ℝ) / (1 / 8 : ℝ)) := by gcongr
      _ = 8 * (Real.exp 1 * ((A : ℝ) + 1)) ^ (1 / 8 : ℝ) *
          (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt q := by
        rw [show Real.exp 1 * (((A : ℝ) + 1) * n ^ 2 / q ^ 4) =
            (Real.exp 1 * ((A : ℝ) + 1)) * n ^ 2 / q ^ 4 by ring,
          rpow_one_eighth_mul_sq_div_fourth_alt (by positivity) (Nat.cast_nonneg n) hqR]
        have hsqrt : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hqR).ne'
        have hsquare := Real.sq_sqrt hqR.le
        field_simp [hsqrt]
        rw [← hsquare, Real.sqrt_sq (Real.sqrt_nonneg q)]
        ring

private lemma mul_quarter_div_self_eq {K x y : ℝ}
    (hK : 0 ≤ K) (hx : 0 < x) (hy : 0 ≤ y) :
    x * (K * y / x) ^ (1 / 4 : ℝ) =
      (K * x ^ 3 * y) ^ (1 / 4 : ℝ) := by
  rw [Real.div_rpow (mul_nonneg hK hy) hx.le,
    Real.mul_rpow hK hy,
    Real.mul_rpow (mul_nonneg hK (by positivity : 0 ≤ x ^ 3)) hy,
    Real.mul_rpow hK (by positivity : 0 ≤ x ^ 3),
    ← Real.rpow_natCast_mul hx.le 3 (1 / 4 : ℝ)]
  have hxq : x ^ (1 / 4 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hxdiv : x / x ^ (1 / 4 : ℝ) = x ^ (3 / 4 : ℝ) := by
    rw [div_eq_iff hxq, ← Real.rpow_add hx]
    norm_num
  calc
    x * (K ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) /
        x ^ (1 / 4 : ℝ)) =
        K ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) *
          (x / x ^ (1 / 4 : ℝ)) := by ring
    _ = K ^ (1 / 4 : ℝ) * x ^ ((3 : ℝ) * (1 / 4 : ℝ)) *
        y ^ (1 / 4 : ℝ) := by
      rw [hxdiv]
      have hexp : (3 / 4 : ℝ) = (3 : ℝ) * (1 / 4 : ℝ) := by norm_num
      conv_lhs => rw [hexp]
      ring

private lemma rpow_one_fourth_mul_cube_div_sq_alt {K x y : ℝ}
    (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 < y) :
    (K * x ^ 3 / y ^ 2) ^ (1 / 4 : ℝ) =
      K ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) / Real.sqrt y := by
  rw [Real.div_rpow (mul_nonneg hK (by positivity)) (by positivity),
    Real.mul_rpow hK (by positivity : 0 ≤ x ^ 3),
    ← Real.rpow_natCast_mul hx 3 (1 / 4 : ℝ),
    ← Real.rpow_natCast_mul hy.le 2 (1 / 4 : ℝ),
    Real.sqrt_eq_rpow]
  norm_num

/-- The pointwise high-range majorant used by the geometric-tail lemma. -/
lemma dyadicAnalyticExponentAlt_le_high (A n i : ℕ)
    (hhi : n < dyadicScale i ^ 2) :
    dyadicAnalyticExponentAlt A n i ≤
      4 * (Real.exp 1 * (A : ℝ) ^ 3 * ((A : ℝ) + 1)) ^ (1 / 4 : ℝ) *
        (n : ℝ) ^ (3 / 4 : ℝ) *
          (Real.sqrt (dyadicScale i))⁻¹ := by
  let q := dyadicScale i
  let c := dyadicAnalyticCapAlt A n i
  have hq : 0 < q := dyadicScale_pos i
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhiR : (n : ℝ) ≤ q ^ 2 := by exact_mod_cast hhi.le
  by_cases hc : c = 0
  · rw [show dyadicAnalyticExponentAlt A n i = 0 by
      simp [dyadicAnalyticExponentAlt, c, hc]]
    positivity
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc
    have hcRpos : (0 : ℝ) < c := by exact_mod_cast hcpos
    have hcR : (c : ℝ) ≤ (A : ℝ) * (n : ℝ) / q := by
      rw [show c = A * n / q by
        dsimp [c, q]
        exact dyadicAnalyticCapAlt_of_lt_sq hhi]
      calc
        ((A * n / q : ℕ) : ℝ) ≤ ((A * n : ℕ) : ℝ) / q := Nat.cast_div_le
        _ = (A : ℝ) * n / q := by norm_num
    have hcMul : (c : ℝ) * q ≤ A * (n : ℝ) := by
      calc
        (c : ℝ) * q ≤ ((A : ℝ) * n / q) * q :=
          mul_le_mul_of_nonneg_right hcR hqR.le
        _ = A * n := by field_simp
    have hcAq : (c : ℝ) ≤ A * q := by
      have hAn : (A : ℝ) * n ≤ A * q ^ 2 :=
        mul_le_mul_of_nonneg_left hhiR (Nat.cast_nonneg A)
      by_contra hnot
      have hgt : (A : ℝ) * q < c := lt_of_not_ge hnot
      nlinarith
    have hsum : (q : ℝ) + c ≤ ((A : ℝ) + 1) * q := by nlinarith
    have hcCube : ((c : ℝ) * q) ^ 3 ≤ (A * (n : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hcMul 3
    have hprod : (c : ℝ) ^ 3 * (q + c) * q ^ 2 ≤
        (A : ℝ) ^ 3 * ((A : ℝ) + 1) * n ^ 3 := by
      calc
        (c : ℝ) ^ 3 * (q + c) * q ^ 2 ≤
            c ^ 3 * (((A : ℝ) + 1) * q) * q ^ 2 := by gcongr
        _ = ((A : ℝ) + 1) * (c * q) ^ 3 := by ring
        _ ≤ ((A : ℝ) + 1) * (A * (n : ℝ)) ^ 3 := by gcongr
        _ = (A : ℝ) ^ 3 * ((A : ℝ) + 1) * n ^ 3 := by ring
    have hbase : Real.exp 1 * (c : ℝ) ^ 3 * (q + c) ≤
        Real.exp 1 * ((A : ℝ) ^ 3 * ((A : ℝ) + 1) * n ^ 3 / q ^ 2) := by
      calc
        Real.exp 1 * (c : ℝ) ^ 3 * (q + c) ≤
            (Real.exp 1 * ((A : ℝ) ^ 3 * ((A : ℝ) + 1) * n ^ 3) /
              q ^ 2) := by
          rw [le_div_iff₀ (sq_pos_of_pos hqR)]
          have ht := mul_le_mul_of_nonneg_left hprod (Real.exp_pos 1).le
          nlinarith
        _ = Real.exp 1 *
            ((A : ℝ) ^ 3 * ((A : ℝ) + 1) * n ^ 3 / q ^ 2) := by ring
    have hrpow := Real.rpow_le_rpow (by positivity) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [show dyadicAnalyticExponentAlt A n i =
        (c : ℝ) *
          ((Real.exp 1 * (((q + c : ℕ) : ℝ) / c)) ^ (1 / 4 : ℝ) /
            (1 / 4 : ℝ)) by
      simp only [dyadicAnalyticExponentAlt, q, c, hc, if_false,
        Nat.not_le_of_lt hhi, if_false]
      field_simp]
    rw [show (Real.exp 1 * (((q + c : ℕ) : ℝ) / c)) =
        Real.exp 1 * ((q : ℝ) + c) / c by norm_num; ring]
    have hquarter := mul_quarter_div_self_eq (K := Real.exp 1)
      (x := (c : ℝ)) (y := (q : ℝ) + c)
      (Real.exp_pos 1).le hcRpos (by positivity)
    calc
      (c : ℝ) *
          ((Real.exp 1 * ((q : ℝ) + c) / c) ^ (1 / 4 : ℝ) /
            (1 / 4 : ℝ)) =
          4 * (c * (Real.exp 1 * ((q : ℝ) + c) / c) ^
            (1 / 4 : ℝ)) := by ring
      _ = 4 * (Real.exp 1 * (c : ℝ) ^ 3 * (q + c)) ^
          (1 / 4 : ℝ) := by rw [hquarter]
    calc
      4 * (Real.exp 1 * (c : ℝ) ^ 3 * (q + c)) ^ (1 / 4 : ℝ) ≤
          4 * (Real.exp 1 *
            ((A : ℝ) ^ 3 * ((A : ℝ) + 1) * n ^ 3 / q ^ 2)) ^
              (1 / 4 : ℝ) := by gcongr
      _ = 4 * (Real.exp 1 * (A : ℝ) ^ 3 * ((A : ℝ) + 1)) ^
            (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) *
              (Real.sqrt q)⁻¹ := by
        rw [show Real.exp 1 *
              ((A : ℝ) ^ 3 * ((A : ℝ) + 1) * n ^ 3 / q ^ 2) =
            (Real.exp 1 * (A : ℝ) ^ 3 * ((A : ℝ) + 1)) * n ^ 3 /
              q ^ 2 by ring,
          rpow_one_fourth_mul_cube_div_sq_alt (by positivity) (Nat.cast_nonneg n) hqR]
        simp only [div_eq_mul_inv]
        ring

lemma dyadicScale_add (a j : ℕ) :
    dyadicScale (a + j) = dyadicScale a * 2 ^ j := by
  simp only [dyadicScale, pow_add]
  ring

lemma dyadicScale_succ (i : ℕ) :
    dyadicScale (i + 1) = 2 * dyadicScale i := by
  simp [dyadicScale, pow_succ, Nat.mul_comm]

private lemma four_thirds_mul_sqrt_le_sqrt_two_mul (x : ℝ) :
    (4 / 3 : ℝ) * Real.sqrt x ≤ Real.sqrt (2 * x) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2 : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  exact mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg x)

private lemma sqrt_dyadicScale_growth (i : ℕ) :
    (4 / 3 : ℝ) * Real.sqrt (dyadicScale i) ≤
      Real.sqrt (dyadicScale (i + 1)) := by
  rw [dyadicScale_succ]
  convert four_thirds_mul_sqrt_le_sqrt_two_mul (dyadicScale i : ℝ) using 1
  all_goals norm_num

private lemma inv_sqrt_dyadicScale_decay (i : ℕ) :
    (Real.sqrt (dyadicScale (i + 1) : ℝ))⁻¹ ≤
      (3 / 4 : ℝ) * (Real.sqrt (dyadicScale i : ℝ))⁻¹ := by
  have hg := sqrt_dyadicScale_growth i
  have h0 : 0 < Real.sqrt (dyadicScale i : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast dyadicScale_pos i)
  have h1 : 0 < Real.sqrt (dyadicScale (i + 1) : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast dyadicScale_pos (i + 1))
  have h43 : 0 < (4 / 3 : ℝ) * Real.sqrt (dyadicScale i : ℝ) :=
    mul_pos (by norm_num) h0
  calc
    (Real.sqrt (dyadicScale (i + 1) : ℝ))⁻¹ ≤
        ((4 / 3 : ℝ) * Real.sqrt (dyadicScale i : ℝ))⁻¹ :=
      (inv_le_inv₀ h1 h43).2 hg
    _ = (3 / 4 : ℝ) * (Real.sqrt (dyadicScale i : ℝ))⁻¹ := by
      field_simp

/-- A geometric-prefix estimate with a rational constant. -/
lemma sum_sqrt_dyadicScale_range (b : ℕ) :
    ∑ i ∈ Finset.range b, Real.sqrt (dyadicScale i : ℝ) ≤
      if b = 0 then 0 else 4 * Real.sqrt (dyadicScale (b - 1) : ℝ) := by
  induction b with
  | zero => simp
  | succ b ih =>
      by_cases hb : b = 0
      · subst b
        simp
        have : 0 ≤ Real.sqrt (dyadicScale 0 : ℝ) := Real.sqrt_nonneg _
        linarith
      · rw [Finset.sum_range_succ, if_neg (Nat.succ_ne_zero b), Nat.succ_sub_one]
        rw [if_neg hb] at ih
        have hg := sqrt_dyadicScale_growth (b - 1)
        have hs : dyadicScale ((b - 1) + 1) = dyadicScale b := by
          congr 1
          omega
        rw [hs] at hg
        calc
          ∑ i ∈ Finset.range b, Real.sqrt (dyadicScale i : ℝ) +
                Real.sqrt (dyadicScale b : ℝ)
              ≤ 4 * Real.sqrt (dyadicScale (b - 1) : ℝ) +
                Real.sqrt (dyadicScale b : ℝ) := by gcongr
          _ ≤ 4 * Real.sqrt (dyadicScale b : ℝ) := by nlinarith

/-- A finite geometric-tail estimate, uniform in the length of the tail. -/
lemma sum_inv_sqrt_dyadicScale_tail (a b : ℕ) :
    ∑ j ∈ Finset.range b,
        (Real.sqrt (dyadicScale (a + j) : ℝ))⁻¹ ≤
      4 * (Real.sqrt (dyadicScale a : ℝ))⁻¹ := by
  induction b generalizing a with
  | zero => positivity
  | succ b ih =>
      rw [Finset.sum_range_succ']
      have htail :
          ∑ j ∈ Finset.range b,
              (Real.sqrt (dyadicScale (a + (j + 1)) : ℝ))⁻¹ ≤
            4 * (Real.sqrt (dyadicScale (a + 1) : ℝ))⁻¹ := by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (a + 1)
      have hdecay := inv_sqrt_dyadicScale_decay a
      calc
        ∑ j ∈ Finset.range b,
              (Real.sqrt (dyadicScale (a + (j + 1)) : ℝ))⁻¹ +
              (Real.sqrt (dyadicScale (a + 0) : ℝ))⁻¹
            ≤ 4 * (Real.sqrt (dyadicScale (a + 1) : ℝ))⁻¹ +
                (Real.sqrt (dyadicScale a : ℝ))⁻¹ := by
              simp only [Nat.add_zero]
              gcongr
        _ ≤ 4 * (Real.sqrt (dyadicScale a : ℝ))⁻¹ := by nlinarith

/-- The low dyadic square-root weights form a prefix and have total size
`O(n^(1/4))`. -/
lemma sum_low_sqrt_dyadicScale (n b : ℕ) :
    ∑ i ∈ Finset.range b,
        (if dyadicScale i ^ 2 ≤ n then Real.sqrt (dyadicScale i : ℝ) else 0) ≤
      4 * Real.sqrt (Real.sqrt n) := by
  induction b with
  | zero => positivity
  | succ b ih =>
      rw [Finset.sum_range_succ]
      by_cases hb : dyadicScale b ^ 2 ≤ n
      · rw [if_pos hb]
        have hpoint :
            ∑ i ∈ Finset.range b,
                (if dyadicScale i ^ 2 ≤ n then
                  Real.sqrt (dyadicScale i : ℝ) else 0) ≤
              ∑ i ∈ Finset.range b, Real.sqrt (dyadicScale i : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          split_ifs <;> simp
        have hfull := sum_sqrt_dyadicScale_range (b + 1)
        rw [if_neg (Nat.succ_ne_zero b), Nat.succ_sub_one] at hfull
        rw [Finset.sum_range_succ] at hfull
        have hq_sqrt : (dyadicScale b : ℝ) ≤ Real.sqrt n := by
          apply Real.le_sqrt_of_sq_le
          exact_mod_cast hb
        have hsqrt : Real.sqrt (dyadicScale b : ℝ) ≤
            Real.sqrt (Real.sqrt n) := Real.sqrt_le_sqrt hq_sqrt
        calc
          ∑ i ∈ Finset.range b,
                (if dyadicScale i ^ 2 ≤ n then
                  Real.sqrt (dyadicScale i : ℝ) else 0) +
                Real.sqrt (dyadicScale b : ℝ)
              ≤ ∑ i ∈ Finset.range b, Real.sqrt (dyadicScale i : ℝ) +
                Real.sqrt (dyadicScale b : ℝ) := by gcongr
          _ ≤ 4 * Real.sqrt (dyadicScale b : ℝ) := hfull
          _ ≤ 4 * Real.sqrt (Real.sqrt n) := by gcongr
      · rw [if_neg hb]
        simpa using ih

/-- The high inverse-square-root weights form a suffix and have total size
`O(n^(-1/4))`. -/
lemma sum_high_inv_sqrt_dyadicScale (n a b : ℕ) (hn : 0 < n) :
    ∑ j ∈ Finset.range b,
        (if n < dyadicScale (a + j) ^ 2 then
          (Real.sqrt (dyadicScale (a + j) : ℝ))⁻¹ else 0) ≤
      4 * (Real.sqrt (Real.sqrt n))⁻¹ := by
  induction b generalizing a with
  | zero => positivity
  | succ b ih =>
      by_cases ha : n < dyadicScale a ^ 2
      · have hpoint :
            ∑ j ∈ Finset.range (b + 1),
                (if n < dyadicScale (a + j) ^ 2 then
                  (Real.sqrt (dyadicScale (a + j) : ℝ))⁻¹ else 0) ≤
              ∑ j ∈ Finset.range (b + 1),
                (Real.sqrt (dyadicScale (a + j) : ℝ))⁻¹ := by
          apply Finset.sum_le_sum
          intro j hj
          split_ifs <;> simp
        have htail := sum_inv_sqrt_dyadicScale_tail a (b + 1)
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hqR : (0 : ℝ) < dyadicScale a := by
          exact_mod_cast dyadicScale_pos a
        have hsqrt_lt : Real.sqrt (n : ℝ) < dyadicScale a := by
          rw [Real.sqrt_lt (by positivity) (by positivity)]
          exact_mod_cast ha
        have hsqrt_sqrt : Real.sqrt (Real.sqrt n) ≤
            Real.sqrt (dyadicScale a : ℝ) :=
          Real.sqrt_le_sqrt hsqrt_lt.le
        have hleft : 0 < Real.sqrt (Real.sqrt n) := by positivity
        have hright : 0 < Real.sqrt (dyadicScale a : ℝ) := by positivity
        have hinv : (Real.sqrt (dyadicScale a : ℝ))⁻¹ ≤
            (Real.sqrt (Real.sqrt n))⁻¹ :=
          (inv_le_inv₀ hright hleft).2 hsqrt_sqrt
        exact hpoint.trans (htail.trans (by gcongr))
      · rw [Finset.sum_range_succ']
        simp only [if_neg ha, add_zero]
        have htail := ih (a + 1)
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htail

end

end Erdos733
