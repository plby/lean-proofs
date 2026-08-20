/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.ShiftedAbelConvolution
import ErdosProblems.Erdos446.UpperStirlingSuppression

/-!
# Erdős Problem 446: numerical normalization of the crowding convolution

After the four-factor split in Ford's (32g), Abel convolution leaves the
factor

`(v+1)^(k-g) / (k+1-g)!`.

In the low-cardinality range `k ≤ 10v`, this is bounded by an absolute
exponential constant, `11^g`, and the natural multinomial normalization
`v^k/(k+1)!`.  Keeping the latter factorial is essential: it is the extra
`1/(k+1)` which the coarse one-barrier proof loses.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Replacing `v` by `v+1` in at most `10v` factors costs only `exp 10`. -/
theorem add_one_pow_le_exp_ten_mul_pow
    {v e : ℕ} (hv : 0 < v) (he : e ≤ 10 * v) :
    (((v + 1 : ℕ) : ℝ) ^ e) ≤ Real.exp 10 * (v : ℝ) ^ e := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have heR : (e : ℝ) ≤ 10 * (v : ℝ) := by exact_mod_cast he
  have hz : 0 ≤ (1 : ℝ) / (v : ℝ) := by positivity
  have hbaseExp : 1 + (1 : ℝ) / (v : ℝ) ≤
      Real.exp ((1 : ℝ) / (v : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp ((1 : ℝ) / (v : ℝ))
  have harg : (e : ℝ) * ((1 : ℝ) / (v : ℝ)) ≤ 10 := by
    rw [mul_one_div]
    exact (div_le_iff₀ hvR).2 heR
  have hfactor : (1 + (1 : ℝ) / (v : ℝ)) ^ e ≤ Real.exp 10 := by
    calc
      (1 + (1 : ℝ) / (v : ℝ)) ^ e ≤
          (Real.exp ((1 : ℝ) / (v : ℝ))) ^ e :=
        pow_le_pow_left₀ (by positivity) hbaseExp e
      _ = Real.exp ((e : ℝ) * ((1 : ℝ) / (v : ℝ))) := by
        rw [Real.exp_nat_mul]
      _ ≤ Real.exp 10 := Real.exp_le_exp.mpr harg
  have hrewrite : (((v + 1 : ℕ) : ℝ)) =
      (v : ℝ) * (1 + (1 : ℝ) / (v : ℝ)) := by
    push_cast
    field_simp
  rw [hrewrite, mul_pow]
  calc
    (v : ℝ) ^ e * (1 + 1 / (v : ℝ)) ^ e ≤
        (v : ℝ) ^ e * Real.exp 10 :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = Real.exp 10 * (v : ℝ) ^ e := by ring

/-- The missing factorial ratio has only `g` factors, each at most `k+1`;
under `k ≤ 10v`, each is at most `11v`. -/
theorem factorial_ratio_le_eleven_pow
    {k v g : ℕ} (hv : 0 < v) (_hg : g ≤ k) (hkv : k ≤ 10 * v) :
    ((k + 1).descFactorial g : ℝ) ≤
      (11 : ℝ) ^ g * (v : ℝ) ^ g := by
  have hnat : k + 1 ≤ 11 * v := by
    have hv1 : 1 ≤ v := hv
    omega
  have hcast : ((k + 1 : ℕ) : ℝ) ≤ 11 * (v : ℝ) := by
    exact_mod_cast hnat
  calc
    ((k + 1).descFactorial g : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ g := by
      exact_mod_cast Nat.descFactorial_le_pow (k + 1) g
    _ ≤ (11 * (v : ℝ)) ^ g :=
      pow_le_pow_left₀ (by positivity) hcast g
    _ = (11 : ℝ) ^ g * (v : ℝ) ^ g := by rw [mul_pow]

/-- A sharper-base version of the factorial-ratio estimate.  The harmless
replacement of `k+1` by `10v+1` is absorbed into `exp 3`, leaving the base
`10^g` required by Ford's factorial-suppression calculation. -/
theorem factorial_ratio_le_exp_three_ten_pow
    {k v g : ℕ} (hv : 0 < v) (hg : g ≤ k) (hkv : k ≤ 10 * v) :
    ((k + 1).descFactorial g : ℝ) ≤
      Real.exp 3 * (10 : ℝ) ^ g * (v : ℝ) ^ g := by
  by_cases hg0 : g = 0
  · subst g
    simp
  have hgpos : 0 < g := Nat.pos_of_ne_zero hg0
  have hknat : k + 1 ≤ 10 * v + 1 := Nat.add_le_add_right hkv 1
  have hkreal : ((k + 1 : ℕ) : ℝ) ≤ (10 * v + 1 : ℕ) := by
    exact_mod_cast hknat
  have hgreal : (g : ℝ) ≤ 10 * (v : ℝ) := by
    exact_mod_cast hg.trans hkv
  have hNpos : 0 ≤ (10 : ℝ) * (v : ℝ) := by positivity
  have hplus : (((10 * v + 1 : ℕ) : ℝ)) ≤
      (10 : ℝ) * (v : ℝ) + 3 := by
    push_cast
    linarith
  have hadd := add_three_pow_le_exp_three_mul_pow g hgpos hgreal
  calc
    ((k + 1).descFactorial g : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ g := by
      exact_mod_cast Nat.descFactorial_le_pow (k + 1) g
    _ ≤ (((10 * v + 1 : ℕ) : ℝ)) ^ g :=
      pow_le_pow_left₀ (by positivity) hkreal g
    _ ≤ ((10 : ℝ) * (v : ℝ) + 3) ^ g :=
      pow_le_pow_left₀ (by positivity) hplus g
    _ ≤ Real.exp 3 * ((10 : ℝ) * (v : ℝ)) ^ g := hadd
    _ = Real.exp 3 * (10 : ℝ) ^ g * (v : ℝ) ^ g := by
      rw [mul_pow]
      ring

/-- The Abel output in (32h), converted to Ford's final factorial
normalization.  The constants `exp 10` and `11^g` are deliberately coarse
but uniform. -/
theorem crowdingAbelFactor_le_normalized
    {k v g : ℕ} (hv : 0 < v) (hg : g ≤ k) (hkv : k ≤ 10 * v) :
    (((v + 1 : ℕ) : ℝ) ^ (k - g) /
        (((k + 1 - g).factorial : ℕ) : ℝ)) ≤
      Real.exp 10 * (11 : ℝ) ^ g * (v : ℝ) ^ k /
        (((k + 1).factorial : ℕ) : ℝ) := by
  have hgn : g ≤ k + 1 := hg.trans (Nat.le_succ k)
  have he : k - g ≤ 10 * v := (Nat.sub_le k g).trans hkv
  have hpow := add_one_pow_le_exp_ten_mul_pow hv he
  have hdesc := factorial_ratio_le_eleven_pow hv hg hkv
  have hfacNat := Nat.factorial_mul_descFactorial hgn
  have hfac :
      ((((k + 1 - g).factorial : ℕ) : ℝ)) *
          (((k + 1).descFactorial g : ℕ) : ℝ) =
        (((k + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast hfacNat
  have hfac0 : (0 : ℝ) < (((k + 1).factorial : ℕ) : ℝ) := by positivity
  have hsmall0 : (0 : ℝ) < (((k + 1 - g).factorial : ℕ) : ℝ) := by
    positivity
  have hnum :
      (((v + 1 : ℕ) : ℝ) ^ (k - g)) *
          (((k + 1).descFactorial g : ℕ) : ℝ) ≤
        Real.exp 10 * (11 : ℝ) ^ g * (v : ℝ) ^ k := by
    calc
      (((v + 1 : ℕ) : ℝ) ^ (k - g)) *
            (((k + 1).descFactorial g : ℕ) : ℝ) ≤
          (Real.exp 10 * (v : ℝ) ^ (k - g)) *
            (((k + 1).descFactorial g : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ (Real.exp 10 * (v : ℝ) ^ (k - g)) *
            ((11 : ℝ) ^ g * (v : ℝ) ^ g) :=
        mul_le_mul_of_nonneg_left hdesc (by positivity)
      _ = Real.exp 10 * (11 : ℝ) ^ g * (v : ℝ) ^ k := by
        calc
          (Real.exp 10 * (v : ℝ) ^ (k - g)) *
                ((11 : ℝ) ^ g * (v : ℝ) ^ g) =
              Real.exp 10 * (11 : ℝ) ^ g *
                ((v : ℝ) ^ (k - g) * (v : ℝ) ^ g) := by ring
          _ = Real.exp 10 * (11 : ℝ) ^ g * (v : ℝ) ^ k := by
            rw [← pow_add, Nat.sub_add_cancel hg]
  have hrewrite :
      (((v + 1 : ℕ) : ℝ) ^ (k - g) /
          (((k + 1 - g).factorial : ℕ) : ℝ)) =
        ((((v + 1 : ℕ) : ℝ) ^ (k - g)) *
          (((k + 1).descFactorial g : ℕ) : ℝ)) /
            (((k + 1).factorial : ℕ) : ℝ) := by
    apply (div_eq_div_iff hsmall0.ne' hfac0.ne').2
    rw [← hfac]
    ring
  rw [hrewrite]
  exact div_le_div_of_nonneg_right hnum hfac0.le

/-- Form with the `exp 4` constant supplied directly by Abel's convolution
bound. -/
theorem crowdingAbelExpFactor_le_normalized
    {k v g : ℕ} (hv : 0 < v) (hg : g ≤ k) (hkv : k ≤ 10 * v) :
    Real.exp 4 *
        (((v + 1 : ℕ) : ℝ) ^ (k - g) /
          (((k + 1 - g).factorial : ℕ) : ℝ)) ≤
      Real.exp 14 * (11 : ℝ) ^ g * (v : ℝ) ^ k /
        (((k + 1).factorial : ℕ) : ℝ) := by
  have h := crowdingAbelFactor_le_normalized hv hg hkv
  calc
    Real.exp 4 *
          (((v + 1 : ℕ) : ℝ) ^ (k - g) /
            (((k + 1 - g).factorial : ℕ) : ℝ)) ≤
        Real.exp 4 *
          (Real.exp 10 * (11 : ℝ) ^ g * (v : ℝ) ^ k /
            (((k + 1).factorial : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos 4).le
    _ = Real.exp 14 * (11 : ℝ) ^ g * (v : ℝ) ^ k /
          (((k + 1).factorial : ℕ) : ℝ) := by
      have hexp : Real.exp 4 * Real.exp 10 = Real.exp 14 := by
        rw [← Real.exp_add]
        norm_num
      rw [← hexp]
      ring

/-- Sharp-base normalization used in the actual crowding estimate.  The
constant is `exp 17`, but the scale depending on `g` is exactly `10^g`.
This is what combines with `(s+1)^g` to give Ford's
`(10(s+1))^g/(g-2)!`. -/
theorem crowdingAbelExpFactor_le_normalized_ten
    {k v g : ℕ} (hv : 0 < v) (hg : g ≤ k) (hkv : k ≤ 10 * v) :
    Real.exp 4 *
        (((v + 1 : ℕ) : ℝ) ^ (k - g) /
          (((k + 1 - g).factorial : ℕ) : ℝ)) ≤
      Real.exp 17 * (10 : ℝ) ^ g * (v : ℝ) ^ k /
        (((k + 1).factorial : ℕ) : ℝ) := by
  have hgn : g ≤ k + 1 := hg.trans (Nat.le_succ k)
  have he : k - g ≤ 10 * v := (Nat.sub_le k g).trans hkv
  have hpow := add_one_pow_le_exp_ten_mul_pow hv he
  have hdesc := factorial_ratio_le_exp_three_ten_pow hv hg hkv
  have hfacNat := Nat.factorial_mul_descFactorial hgn
  have hfac :
      ((((k + 1 - g).factorial : ℕ) : ℝ)) *
          (((k + 1).descFactorial g : ℕ) : ℝ) =
        (((k + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast hfacNat
  have hfac0 : (0 : ℝ) < (((k + 1).factorial : ℕ) : ℝ) := by positivity
  have hsmall0 : (0 : ℝ) < (((k + 1 - g).factorial : ℕ) : ℝ) := by
    positivity
  have hnum :
      Real.exp 4 * (((v + 1 : ℕ) : ℝ) ^ (k - g)) *
          (((k + 1).descFactorial g : ℕ) : ℝ) ≤
        Real.exp 17 * (10 : ℝ) ^ g * (v : ℝ) ^ k := by
    calc
      Real.exp 4 * (((v + 1 : ℕ) : ℝ) ^ (k - g)) *
            (((k + 1).descFactorial g : ℕ) : ℝ) ≤
          Real.exp 4 * (Real.exp 10 * (v : ℝ) ^ (k - g)) *
            (((k + 1).descFactorial g : ℕ) : ℝ) := by
        gcongr
      _ ≤ Real.exp 4 * (Real.exp 10 * (v : ℝ) ^ (k - g)) *
            (Real.exp 3 * (10 : ℝ) ^ g * (v : ℝ) ^ g) := by
        gcongr
      _ = Real.exp 17 * (10 : ℝ) ^ g * (v : ℝ) ^ k := by
        have hexp : Real.exp 4 * Real.exp 10 * Real.exp 3 =
            Real.exp 17 := by
          rw [← Real.exp_add, ← Real.exp_add]
          norm_num
        calc
          Real.exp 4 * (Real.exp 10 * (v : ℝ) ^ (k - g)) *
                (Real.exp 3 * (10 : ℝ) ^ g * (v : ℝ) ^ g) =
              (Real.exp 4 * Real.exp 10 * Real.exp 3) *
                (10 : ℝ) ^ g *
                  ((v : ℝ) ^ (k - g) * (v : ℝ) ^ g) := by ring
          _ = Real.exp 17 * (10 : ℝ) ^ g * (v : ℝ) ^ k := by
            rw [hexp, ← pow_add, Nat.sub_add_cancel hg]
  have hrewrite :
      Real.exp 4 *
          (((v + 1 : ℕ) : ℝ) ^ (k - g) /
            (((k + 1 - g).factorial : ℕ) : ℝ)) =
        (Real.exp 4 * (((v + 1 : ℕ) : ℝ) ^ (k - g)) *
          (((k + 1).descFactorial g : ℕ) : ℝ)) /
            (((k + 1).factorial : ℕ) : ℝ) := by
    field_simp
    rw [← hfac]
  rw [hrewrite]
  exact div_le_div_of_nonneg_right hnum hfac0.le

/-- Uniform version allowing the Abel argument to enlarge its second affine
base from zero to one in the negative-parameter case.  That enlargement
changes `v+1` to `v+2` and costs one further factor `exp 10`; the crucial
base `10^g` and denominator `(k+1)!` are unchanged. -/
theorem crowdingAbelExpFactor_le_normalized_ten_add_two
    {k v g : ℕ} (hv : 0 < v) (hg : g ≤ k) (hkv : k ≤ 10 * v) :
    Real.exp 4 *
        (((v + 2 : ℕ) : ℝ) ^ (k - g) /
          (((k + 1 - g).factorial : ℕ) : ℝ)) ≤
      Real.exp 27 * (10 : ℝ) ^ g * (v : ℝ) ^ k /
        (((k + 1).factorial : ℕ) : ℝ) := by
  have he : k - g ≤ 10 * (v + 1) := by omega
  have hadd := add_one_pow_le_exp_ten_mul_pow
    (v := v + 1) (e := k - g) (by omega) he
  have hden : 0 ≤ (((k + 1 - g).factorial : ℕ) : ℝ) := by positivity
  have hquot :
      (((v + 2 : ℕ) : ℝ) ^ (k - g) /
          (((k + 1 - g).factorial : ℕ) : ℝ)) ≤
        Real.exp 10 *
          (((v + 1 : ℕ) : ℝ) ^ (k - g) /
            (((k + 1 - g).factorial : ℕ) : ℝ)) := by
    calc
      (((v + 2 : ℕ) : ℝ) ^ (k - g) /
            (((k + 1 - g).factorial : ℕ) : ℝ)) ≤
          (Real.exp 10 * ((v + 1 : ℕ) : ℝ) ^ (k - g)) /
            (((k + 1 - g).factorial : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hden
        simpa only [Nat.add_assoc] using hadd
      _ = Real.exp 10 *
          (((v + 1 : ℕ) : ℝ) ^ (k - g) /
            (((k + 1 - g).factorial : ℕ) : ℝ)) := by ring
  have hbase := crowdingAbelExpFactor_le_normalized_ten hv hg hkv
  calc
    Real.exp 4 *
          (((v + 2 : ℕ) : ℝ) ^ (k - g) /
            (((k + 1 - g).factorial : ℕ) : ℝ)) ≤
        Real.exp 4 *
          (Real.exp 10 *
            (((v + 1 : ℕ) : ℝ) ^ (k - g) /
              (((k + 1 - g).factorial : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hquot (Real.exp_pos 4).le
    _ = Real.exp 10 *
        (Real.exp 4 *
          (((v + 1 : ℕ) : ℝ) ^ (k - g) /
            (((k + 1 - g).factorial : ℕ) : ℝ))) := by ring
    _ ≤ Real.exp 10 *
        (Real.exp 17 * (10 : ℝ) ^ g * (v : ℝ) ^ k /
          (((k + 1).factorial : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos 10).le
    _ = Real.exp 27 * (10 : ℝ) ^ g * (v : ℝ) ^ k /
          (((k + 1).factorial : ℕ) : ℝ) := by
      have hexp : Real.exp 10 * Real.exp 17 = Real.exp 27 := by
        rw [← Real.exp_add]
        norm_num
      rw [← hexp]
      ring

/-! The combination `11^g * (s+1)^g` which occurs downstream is written
as one power so that the factorial-suppression lemma can be applied
directly. -/

theorem eleven_pow_mul_add_pow (g s : ℕ) :
    (11 : ℝ) ^ g * ((s + 1 : ℕ) : ℝ) ^ g =
      ((11 * (s + 1 : ℕ) : ℕ) : ℝ) ^ g := by
  push_cast
  rw [mul_pow]

/-- The complete dyadic crowding factor after substituting
`g = 2^m, s = 2m`.  The `g²/g!` factor costs at most two copies of
`1/(g-2)!`, after which `fordCrowdingFactorialSuppression` applies
verbatim. -/
theorem fordDyadicCrowdingFactor_le_suppressed
    {m : ℕ} (hm : 1 ≤ m) :
    (((2 ^ m : ℕ) : ℝ) ^ 2 *
        (((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m))) /
          (((2 ^ m).factorial : ℕ) : ℝ) ≤
      2 * fordCrowdingSuppressionConstant /
        (2 : ℝ) ^ (2 ^ m) := by
  let n := 2 ^ m
  have hn : 2 ≤ n := by
    dsimp [n]
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
  have hnfac : n.factorial = n * (n - 1) * (n - 2).factorial := by
    have hnrepr : n = (n - 2) + 2 := by omega
    nth_rw 1 [hnrepr]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    have h2 : n - 2 + 2 = n := by omega
    have h1 : n - 2 + 1 = n - 1 := by omega
    rw [h2, h1]
    ring
  have hnratio : n ^ 2 * (n - 2).factorial ≤ 2 * n.factorial := by
    rw [hnfac, pow_two]
    have hnlin : n ≤ 2 * (n - 1) := by omega
    have hmul := Nat.mul_le_mul_right (n * (n - 2).factorial) hnlin
    nlinarith
  have hnratioR :
      ((n : ℝ) ^ 2) * (((n - 2).factorial : ℕ) : ℝ) ≤
        2 * (((n.factorial : ℕ) : ℝ)) := by
    exact_mod_cast hnratio
  have hfac0 : (0 : ℝ) < (((n.factorial : ℕ) : ℝ)) := by positivity
  have hfac20 : (0 : ℝ) < (((n - 2).factorial : ℕ) : ℝ) := by positivity
  have hbase : 0 ≤ (((20 * m + 10 : ℕ) : ℝ) ^ n) := by positivity
  have hratio :
      ((n : ℝ) ^ 2 * (((20 * m + 10 : ℕ) : ℝ) ^ n)) /
          (((n.factorial : ℕ) : ℝ)) ≤
        2 * ((((20 * m + 10 : ℕ) : ℝ) ^ n) /
          (((n - 2).factorial : ℕ) : ℝ)) := by
    rw [show 2 * ((((20 * m + 10 : ℕ) : ℝ) ^ n) /
        (((n - 2).factorial : ℕ) : ℝ)) =
      (2 * (((20 * m + 10 : ℕ) : ℝ) ^ n)) /
        (((n - 2).factorial : ℕ) : ℝ) by ring]
    apply (div_le_div_iff₀ hfac0 hfac20).2
    calc
      ((n : ℝ) ^ 2 * (((20 * m + 10 : ℕ) : ℝ) ^ n)) *
            (((n - 2).factorial : ℕ) : ℝ) =
          (((20 * m + 10 : ℕ) : ℝ) ^ n) *
            (((n : ℝ) ^ 2) * (((n - 2).factorial : ℕ) : ℝ)) := by ring
      _ ≤ (((20 * m + 10 : ℕ) : ℝ) ^ n) *
            (2 * (((n.factorial : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hnratioR hbase
      _ = 2 * ((((20 * m + 10 : ℕ) : ℝ) ^ n)) *
            (((n.factorial : ℕ) : ℝ)) := by ring
  have hsuppress := fordCrowdingFactorialSuppression m
  change (((n : ℕ) : ℝ) ^ 2 *
      (((20 * m + 10 : ℕ) : ℝ) ^ n)) /
        (((n.factorial : ℕ) : ℝ)) ≤ _
  calc
    (((n : ℕ) : ℝ) ^ 2 * (((20 * m + 10 : ℕ) : ℝ) ^ n)) /
          (((n.factorial : ℕ) : ℝ)) ≤
        2 * ((((20 * m + 10 : ℕ) : ℝ) ^ n) /
          (((n - 2).factorial : ℕ) : ℝ)) := hratio
    _ ≤ 2 * (fordCrowdingSuppressionConstant / (2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left (by simpa [n] using hsuppress) (by norm_num)
    _ = 2 * fordCrowdingSuppressionConstant / (2 : ℝ) ^ n := by ring

end Erdos446
