/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Scale
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The Stirling scale in Ford's divisor-interval argument

This file converts the factorial expression occurring at Ford's critical
index into the Erdős--Tenenbaum--Ford logarithmic scale.  In particular,
the index is the genuine natural floor of `log log y / log 2`; no rounding
or change of the limiting filter is hidden in the statement.
-/

namespace Erdos896.Ford

open Filter Asymptotics

/-- Ford's critical factorial index. -/
noncomputable def stirlingIndex (y : ℝ) : ℕ :=
  ⌊Real.log (Real.log y) / Real.log 2⌋₊

/-- The factorial expression at Ford's critical index. -/
noncomputable def stirlingTerm (y : ℝ) : ℝ :=
  (2 * Real.log (Real.log y)) ^ stirlingIndex y /
    ((stirlingIndex y + 1).factorial : ℝ)

/-- The logarithmic power to which the factorial expression is compared. -/
noncomputable def stirlingTarget (y : ℝ) : ℝ :=
  (Real.log y) ^ (2 - Erdos896.delta896) /
    (Real.log (Real.log y)) ^ (3 / 2 : ℝ)

/-- The exponent used here is exactly the Erdős--Tenenbaum--Ford exponent. -/
theorem delta896_formula :
    Erdos896.delta896 =
      1 - (1 + Real.log (Real.log 2)) / Real.log 2 := rfl

/-- The complementary exponent is the logarithm naturally produced by
Stirling's formula. -/
theorem two_sub_delta896 :
    2 - Erdos896.delta896 =
      Real.log (2 * Real.exp 1 * Real.log 2) / Real.log 2 := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have he : Real.exp (1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [delta896_formula, Real.log_mul (mul_ne_zero h2 he) hlog2.ne',
    Real.log_mul h2 he, Real.log_exp]
  field_simp
  ring

/-- The floor index never exceeds its defining real quotient. -/
theorem stirlingIndex_cast_le {y : ℝ}
    (hy : 0 ≤ Real.log (Real.log y)) :
    (stirlingIndex y : ℝ) ≤
      Real.log (Real.log y) / Real.log 2 := by
  exact Nat.floor_le (div_nonneg hy (Real.log_pos one_lt_two).le)

/-- The successor of the floor index strictly exceeds its defining real
quotient. -/
theorem loglog_div_log_two_lt_stirlingIndex_add_one (y : ℝ) :
    Real.log (Real.log y) / Real.log 2 <
      ((stirlingIndex y + 1 : ℕ) : ℝ) := by
  simpa [stirlingIndex] using
    (Nat.lt_floor_add_one (Real.log (Real.log y) / Real.log 2))

/-- A convenient exact algebraic form of the lower Stirling bound. -/
private theorem factorial_step_bound (t : ℝ) (v : ℕ) (ht : 0 ≤ t) :
    (2 * t) ^ v / ((v + 1).factorial : ℝ) ≤
      Real.exp 1 * (2 * Real.exp 1 * t / (v + 1 : ℝ)) ^ v /
        (v + 1 : ℝ) ^ (3 / 2 : ℝ) := by
  let n := v + 1
  have hnpos : 0 < (n : ℝ) := by dsimp [n]; positivity
  have hsqrt : Real.sqrt (n : ℝ) ≤ Real.sqrt (2 * Real.pi * n) := by
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_gt_three]
  have hfactorial :
      Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n ≤
        (n.factorial : ℝ) := by
    exact (mul_le_mul_of_nonneg_right hsqrt (by positivity)).trans
      (Stirling.le_factorial_stirling n)
  have hdenpos :
      0 < Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n := by
    positivity
  calc
    (2 * t) ^ v / ((v + 1).factorial : ℝ) =
        (2 * t) ^ v / (n.factorial : ℝ) := by simp [n]
    _ ≤ (2 * t) ^ v /
        (Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) := by
      exact div_le_div_of_nonneg_left (by positivity) hdenpos hfactorial
    _ = Real.exp 1 * (2 * Real.exp 1 * t / (n : ℝ)) ^ v /
        (n : ℝ) ^ (3 / 2 : ℝ) := by
      have hsqrt_eq :
          (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt n := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add hnpos, Real.rpow_one, Real.sqrt_eq_rpow]
      rw [hsqrt_eq]
      simp only [n, Nat.cast_add, Nat.cast_one, pow_succ,
        div_pow, mul_pow]
      field_simp
    _ = Real.exp 1 *
        (2 * Real.exp 1 * t / (v + 1 : ℝ)) ^ v /
          (v + 1 : ℝ) ^ (3 / 2 : ℝ) := by simp [n]

/-- The matching direction of the elementary Stirling estimate.  The
constant `1 / 2` is deliberately inessential; keeping it explicit makes the
later uniform lower comparison convenient. -/
private theorem factorial_step_lower (t : ℝ) (v : ℕ) (ht : 0 ≤ t) :
    (1 / 2 : ℝ) *
        (2 * Real.exp 1 * t / (v + 1 : ℝ)) ^ v /
          (v + 1 : ℝ) ^ (3 / 2 : ℝ) ≤
      (2 * t) ^ v / ((v + 1).factorial : ℝ) := by
  let n := v + 1
  have hnpos : 0 < (n : ℝ) := by dsimp [n]; positivity
  have hseq : Stirling.stirlingSeq n ≤ Real.exp 1 := by
    calc
      Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
        simpa [n, Function.comp_apply] using
          (Stirling.stirlingSeq'_antitone (Nat.zero_le v))
      _ = Real.exp 1 / Real.sqrt 2 := Stirling.stirlingSeq_one
      _ ≤ Real.exp 1 := div_le_self (Real.exp_pos 1).le (by simp)
  have hstirPos :
      0 < Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n := by
    positivity
  have hfac0 :
      (n.factorial : ℝ) ≤
        Real.exp 1 *
          (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := by
    rw [mul_comm]
    apply (div_le_iff₀' hstirPos).mp
    simpa [Stirling.stirlingSeq] using hseq
  have hsqrt : Real.sqrt (2 * (n : ℝ)) ≤ 2 * Real.sqrt n := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    gcongr
  have hfac :
      (n.factorial : ℝ) ≤
        2 * Real.exp 1 *
          (Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) := by
    calc
      (n.factorial : ℝ) ≤
          Real.exp 1 *
            (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := hfac0
      _ ≤ Real.exp 1 *
            ((2 * Real.sqrt n) * ((n : ℝ) / Real.exp 1) ^ n) := by gcongr
      _ = 2 * Real.exp 1 *
            (Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) := by ring
  have hfacPos : 0 < (n.factorial : ℝ) := by positivity
  have hupperPos :
      0 < 2 * Real.exp 1 *
        (Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) := by
    positivity
  calc
    (1 / 2 : ℝ) *
          (2 * Real.exp 1 * t / (v + 1 : ℝ)) ^ v /
            (v + 1 : ℝ) ^ (3 / 2 : ℝ) =
        (2 * t) ^ v /
          (2 * Real.exp 1 *
            (Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n)) := by
      have hsqrt_eq :
          (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt n := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add hnpos, Real.rpow_one, Real.sqrt_eq_rpow]
      simp only [n, Nat.cast_add, Nat.cast_one] at hsqrt_eq ⊢
      rw [hsqrt_eq]
      simp only [pow_succ, div_pow, mul_pow]
      field_simp
    _ ≤ (2 * t) ^ v / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hfacPos hfac
    _ = (2 * t) ^ v / ((v + 1).factorial : ℝ) := by simp [n]

/-- An explicit positive constant for the reverse comparison. -/
noncomputable def stirlingReverseConstant : ℝ :=
  (1 / 2 : ℝ) *
    (Real.exp (-1) / (2 * Real.exp 1 * Real.log 2)) /
      (2 / Real.log 2) ^ (3 / 2 : ℝ)

theorem stirlingReverseConstant_pos : 0 < stirlingReverseConstant := by
  unfold stirlingReverseConstant
  positivity

/-- Pointwise Stirling conversion on the eventual positive domain. -/
theorem stirlingTerm_le_target {y : ℝ}
    (hy : 1 < Real.log y) :
    stirlingTerm y ≤
      (Real.exp 1 * (Real.log 2) ^ (3 / 2 : ℝ)) * stirlingTarget y := by
  let t := Real.log (Real.log y)
  let v := stirlingIndex y
  let n := v + 1
  let a := 2 * Real.exp 1 * Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogy : 0 < Real.log y := zero_lt_one.trans hy
  have ht : 0 < t := by simpa [t] using Real.log_pos hy
  have hnpos : 0 < (n : ℝ) := by dsimp [n]; positivity
  have ha : 1 < a := by
    have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr zero_lt_one
    have htwo : 1 < 2 * Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    calc
      1 < 2 * Real.log 2 := htwo
      _ < 2 * Real.exp 1 * Real.log 2 := by
        nlinarith
  have hv_le : (v : ℝ) ≤ t / Real.log 2 := by
    simpa [t, v] using stirlingIndex_cast_le ht.le
  have hq_lt : t / Real.log 2 < (n : ℝ) := by
    simpa [t, v, n] using loglog_div_log_two_lt_stirlingIndex_add_one y
  have hbase : 2 * Real.exp 1 * t / (n : ℝ) ≤ a := by
    apply (div_le_iff₀' hnpos).2
    have ht_le : t ≤ (n : ℝ) * Real.log 2 := by
      exact (div_le_iff₀ hlog2).mp hq_lt.le
    calc
      2 * Real.exp 1 * t ≤
          2 * Real.exp 1 * ((n : ℝ) * Real.log 2) := by gcongr
      _ = (n : ℝ) * a := by dsimp [a]; ring
  have hpow_base :
      (2 * Real.exp 1 * t / (n : ℝ)) ^ v ≤ a ^ v := by
    exact pow_le_pow_left₀ (by positivity) hbase v
  have hpow_exp : a ^ v ≤ a ^ (t / Real.log 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ha.le hv_le
  have hpow_target :
      a ^ (t / Real.log 2) =
        (Real.log y) ^ (2 - Erdos896.delta896) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans ha), Real.rpow_def_of_pos hlogy]
    congr 1
    rw [two_sub_delta896]
    dsimp [a, t]
    ring
  have hpow :
      (2 * Real.exp 1 * t / (n : ℝ)) ^ v ≤
        (Real.log y) ^ (2 - Erdos896.delta896) := by
    exact hpow_base.trans (hpow_exp.trans_eq hpow_target)
  have hden : (t / Real.log 2) ^ (3 / 2 : ℝ) ≤
      (n : ℝ) ^ (3 / 2 : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) hq_lt.le (by norm_num)
  have hsmallDen : 0 < (t / Real.log 2) ^ (3 / 2 : ℝ) := by positivity
  have hnDen : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hmain := factorial_step_bound t v ht.le
  rw [stirlingTerm]
  change (2 * t) ^ v / ((v + 1).factorial : ℝ) ≤ _
  calc
    (2 * t) ^ v / ((v + 1).factorial : ℝ) ≤
        Real.exp 1 *
          (2 * Real.exp 1 * t / (n : ℝ)) ^ v /
            (n : ℝ) ^ (3 / 2 : ℝ) := by simpa [n] using hmain
    _ ≤ Real.exp 1 *
          (Real.log y) ^ (2 - Erdos896.delta896) /
            (t / Real.log 2) ^ (3 / 2 : ℝ) := by
      calc
        Real.exp 1 * (2 * Real.exp 1 * t / (n : ℝ)) ^ v /
              (n : ℝ) ^ (3 / 2 : ℝ) ≤
            Real.exp 1 * (Real.log y) ^ (2 - Erdos896.delta896) /
              (n : ℝ) ^ (3 / 2 : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (by positivity)) hnDen.le
        _ ≤ Real.exp 1 *
              (Real.log y) ^ (2 - Erdos896.delta896) /
                (t / Real.log 2) ^ (3 / 2 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hsmallDen hden
    _ = (Real.exp 1 * (Real.log 2) ^ (3 / 2 : ℝ)) *
          stirlingTarget y := by
      rw [stirlingTarget]
      change Real.exp 1 * (Real.log y) ^ (2 - Erdos896.delta896) /
          (Real.log (Real.log y) / Real.log 2) ^ (3 / 2 : ℝ) =
        (Real.exp 1 * Real.log 2 ^ (3 / 2 : ℝ)) *
          (Real.log y ^ (2 - Erdos896.delta896) /
            Real.log (Real.log y) ^ (3 / 2 : ℝ))
      rw [Real.div_rpow ht.le hlog2.le]
      simp only [t]
      field_simp

/-- The reverse pointwise comparison once the critical quotient is at least
one.  Together with `stirlingTerm_le_target`, this records the full exact
Stirling-scale conversion needed by the lower-bound argument. -/
theorem target_le_stirlingTerm {y : ℝ}
    (hy : 1 < Real.log y)
    (hyLarge : Real.log 2 ≤ Real.log (Real.log y)) :
    stirlingReverseConstant * stirlingTarget y ≤ stirlingTerm y := by
  let t := Real.log (Real.log y)
  let v := stirlingIndex y
  let n := v + 1
  let a := 2 * Real.exp 1 * Real.log 2
  let q := t / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogy : 0 < Real.log y := zero_lt_one.trans hy
  have ht : 0 < t := by simpa [t] using Real.log_pos hy
  have hqOne : 1 ≤ q := by
    dsimp [q, t]
    have h : 1 * Real.log 2 ≤ Real.log (Real.log y) := by
      simpa only [one_mul] using hyLarge
    exact (le_div_iff₀ hlog2).2 h
  have hvpos : 0 < v := by
    dsimp [v, stirlingIndex]
    exact Nat.floor_pos.mpr hqOne
  have hvreal : 0 < (v : ℝ) := by exact_mod_cast hvpos
  have hnpos : 0 < (n : ℝ) := by dsimp [n]; positivity
  have ha : 1 < a := by
    have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr zero_lt_one
    have htwo : 1 < 2 * Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    calc
      1 < 2 * Real.log 2 := htwo
      _ < 2 * Real.exp 1 * Real.log 2 := by nlinarith
  have hv_le : (v : ℝ) ≤ q := by
    simpa [q, t, v] using stirlingIndex_cast_le ht.le
  have hq_lt : q < (n : ℝ) := by
    simpa [q, t, v, n] using loglog_div_log_two_lt_stirlingIndex_add_one y
  have hvlog_le : (v : ℝ) * Real.log 2 ≤ t := by
    exact (le_div_iff₀ hlog2).mp hv_le
  have hbaseLower :
      a * ((v : ℝ) / (n : ℝ)) ≤
        2 * Real.exp 1 * t / (n : ℝ) := by
    calc
      a * ((v : ℝ) / (n : ℝ)) = a * (v : ℝ) / (n : ℝ) := by ring
      _ ≤ (2 * Real.exp 1 * t) / (n : ℝ) :=
        div_le_div_of_nonneg_right (by
          calc
            a * (v : ℝ) =
                2 * Real.exp 1 * ((v : ℝ) * Real.log 2) := by dsimp [a]; ring
            _ ≤ 2 * Real.exp 1 * t := by gcongr) hnpos.le
  have hratio :
      Real.exp (-1) ≤ ((v : ℝ) / (n : ℝ)) ^ v := by
    have hstandard := Real.one_add_inv_pow_le_exp (n := v)
    have hbasePos : 0 < 1 + (v : ℝ)⁻¹ := by positivity
    have hinv :
        (Real.exp 1)⁻¹ ≤ ((1 + (v : ℝ)⁻¹) ^ v)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos 1) (pow_pos hbasePos v)).2 hstandard
    rw [Real.exp_neg]
    calc
      (Real.exp 1)⁻¹ ≤ ((1 + (v : ℝ)⁻¹) ^ v)⁻¹ := hinv
      _ = ((v : ℝ) / (n : ℝ)) ^ v := by
        rw [← inv_pow]
        congr 1
        dsimp [n]
        push_cast
        field_simp
  have hbasePow :
      Real.exp (-1) * a ^ v ≤
        (2 * Real.exp 1 * t / (n : ℝ)) ^ v := by
    calc
      Real.exp (-1) * a ^ v ≤
          ((v : ℝ) / (n : ℝ)) ^ v * a ^ v := by gcongr
      _ = (a * ((v : ℝ) / (n : ℝ))) ^ v := by
        rw [mul_pow]
        ring
      _ ≤ (2 * Real.exp 1 * t / (n : ℝ)) ^ v :=
        pow_le_pow_left₀ (by positivity) hbaseLower v
  have htargetEq :
      a ^ q = (Real.log y) ^ (2 - Erdos896.delta896) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans ha), Real.rpow_def_of_pos hlogy]
    congr 1
    rw [two_sub_delta896]
    dsimp [a, q, t]
    ring
  have htargetPow :
      (Real.log y) ^ (2 - Erdos896.delta896) ≤ a ^ n := by
    calc
      (Real.log y) ^ (2 - Erdos896.delta896) = a ^ q := htargetEq.symm
      _ ≤ a ^ (n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ha.le hq_lt.le
      _ = a ^ n := Real.rpow_natCast a n
  have hnumerator :
      (Real.exp (-1) / a) *
          (Real.log y) ^ (2 - Erdos896.delta896) ≤
        (2 * Real.exp 1 * t / (n : ℝ)) ^ v := by
    calc
      (Real.exp (-1) / a) *
            (Real.log y) ^ (2 - Erdos896.delta896) ≤
          (Real.exp (-1) / a) * a ^ n := by gcongr
      _ = Real.exp (-1) * a ^ v := by
        dsimp [n]
        rw [pow_succ]
        field_simp
      _ ≤ (2 * Real.exp 1 * t / (n : ℝ)) ^ v := hbasePow
  have hn_le : (n : ℝ) ≤ 2 * q := by
    have hnEq : (n : ℝ) = (v : ℝ) + 1 := by simp [n]
    linarith [hv_le, hqOne]
  have hden :
      (n : ℝ) ^ (3 / 2 : ℝ) ≤ (2 * q) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hn_le (by norm_num)
  have hnDenPos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hbigDenPos : 0 < (2 * q) ^ (3 / 2 : ℝ) := by positivity
  have hmain := factorial_step_lower t v ht.le
  calc
    stirlingReverseConstant * stirlingTarget y =
        (1 / 2 : ℝ) *
            ((Real.exp (-1) / a) *
              (Real.log y) ^ (2 - Erdos896.delta896)) /
          (2 * q) ^ (3 / 2 : ℝ) := by
      rw [stirlingReverseConstant, stirlingTarget]
      change ((1 / 2 : ℝ) * (Real.exp (-1) / a) /
            (2 / Real.log 2) ^ (3 / 2 : ℝ)) *
          (Real.log y ^ (2 - Erdos896.delta896) /
            t ^ (3 / 2 : ℝ)) = _
      have htwo : 0 ≤ (2 / Real.log 2 : ℝ) := by positivity
      rw [show 2 * q = (2 / Real.log 2) * t by dsimp [q]; ring,
        Real.mul_rpow htwo ht.le]
      field_simp
    _ ≤ (1 / 2 : ℝ) *
          (2 * Real.exp 1 * t / (n : ℝ)) ^ v /
            (2 * q) ^ (3 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnumerator (by norm_num)) hbigDenPos.le
    _ ≤ (1 / 2 : ℝ) *
          (2 * Real.exp 1 * t / (n : ℝ)) ^ v /
            (n : ℝ) ^ (3 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hnDenPos hden
    _ ≤ stirlingTerm y := by
      simpa [stirlingTerm, t, v, n] using hmain

/-- The exact factorial expression at `v = floor (log log y / log 2)` is
big-O of the Ford logarithmic scale. -/
theorem stirlingScale_isBigO :
    stirlingTerm =O[Filter.atTop] stirlingTarget := by
  apply Asymptotics.IsBigO.of_bound
    (Real.exp 1 * (Real.log 2) ^ (3 / 2 : ℝ))
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with y hy
  have hy0 : 0 < y := (Real.exp_pos 1).trans hy
  have hlogy : 1 < Real.log y := (Real.lt_log_iff_exp_lt hy0).2 hy
  have hloglog : 0 < Real.log (Real.log y) := Real.log_pos hlogy
  have hleft : 0 ≤ stirlingTerm y := by
    unfold stirlingTerm
    positivity
  have hright : 0 ≤ stirlingTarget y := by
    unfold stirlingTarget
    positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright,
    Real.norm_of_nonneg (by positivity :
      0 ≤ Real.exp 1 * (Real.log 2) ^ (3 / 2 : ℝ))] using
    (stirlingTerm_le_target hlogy)

/-- Eventual lower comparison in the orientation used by Ford's lower
bound. -/
theorem eventually_const_mul_target_le_stirlingTerm :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ y : ℝ in Filter.atTop, c * stirlingTarget y ≤ stirlingTerm y := by
  refine ⟨stirlingReverseConstant, stirlingReverseConstant_pos, ?_⟩
  filter_upwards [eventually_gt_atTop (Real.exp 2)] with y hy
  have hy0 : 0 < y := (Real.exp_pos 2).trans hy
  have hlogyTwo : 2 < Real.log y :=
    (Real.lt_log_iff_exp_lt hy0).2 hy
  have hloglog : Real.log 2 ≤ Real.log (Real.log y) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
      (Set.mem_Ioi.mpr (by linarith : 0 < Real.log y)) hlogyTwo.le
  exact target_le_stirlingTerm (by linarith) hloglog

/-- The reverse big-O comparison. -/
theorem stirlingTarget_isBigO :
    stirlingTarget =O[Filter.atTop] stirlingTerm := by
  obtain ⟨c, hc, h⟩ := eventually_const_mul_target_le_stirlingTerm
  apply Asymptotics.IsBigO.of_bound c⁻¹
  filter_upwards [h, eventually_gt_atTop (Real.exp 2)] with y hy hyLarge
  have hy0 : 0 < y := (Real.exp_pos 2).trans hyLarge
  have hlogyTwo : 2 < Real.log y :=
    (Real.lt_log_iff_exp_lt hy0).2 hyLarge
  have hleft : 0 ≤ stirlingTarget y := by
    unfold stirlingTarget
    have : 0 < Real.log (Real.log y) := Real.log_pos (by linarith)
    positivity
  have hright : 0 ≤ stirlingTerm y := by
    unfold stirlingTerm
    have : 0 < Real.log (Real.log y) := Real.log_pos (by linarith)
    positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright]
  rw [inv_mul_eq_div]
  exact (le_div_iff₀' hc).2 hy

/-- The factorial expression and the Ford logarithmic scale are of exactly
the same asymptotic order. -/
theorem stirlingScale_isTheta :
    stirlingTerm =Θ[Filter.atTop] stirlingTarget :=
  ⟨stirlingScale_isBigO, stirlingTarget_isBigO⟩

end Erdos896.Ford
