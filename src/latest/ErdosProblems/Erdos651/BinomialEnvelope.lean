/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Definitions
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The binomial estimate in the Pohoata--Zakharov endgame

This file records the rounding-sensitive estimate which changes the binomial
coefficient produced by the cap argument into an envelope of the form
`t ^ (C * n / t)`.  The factorial in the binomial coefficient is essential:
the cruder estimate `choose N a ≤ N^a` would retain an unwanted `log n`.
-/

namespace Erdos651

noncomputable section

/-- The cap size used in the alternating cap assembly. -/
def pzCapSize (n t : ℕ) : ℕ :=
  ⌈(2 : ℝ) * n / t⌉₊

theorem pzCapSize_pos {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    0 < pzCapSize n t := by
  rw [pzCapSize]
  apply Nat.ceil_pos.mpr
  positivity

theorem pzCapSize_lower {n t : ℕ} (ht : 0 < t) :
    (2 : ℝ) * n / t ≤ (pzCapSize n t : ℝ) := by
  exact Nat.le_ceil _

theorem pzCapSize_upper {n t : ℕ} (_ht : 0 < t) :
    (pzCapSize n t : ℝ) < (2 : ℝ) * n / t + 1 := by
  apply Nat.ceil_lt_add_one
  positivity

/-- The elementary real binomial estimate `choose (n+a) a ≤ (e(n+a)/a)^a`.
It is proved from Mathlib's Stirling lower bound. -/
theorem choose_add_le_exp_mul_div_pow (n a : ℕ) (ha : 0 < a) :
    ((Nat.choose (n + a) a : ℕ) : ℝ) ≤
      (Real.exp 1 * ((n + a : ℕ) : ℝ) / (a : ℝ)) ^ a := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * a) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    nlinarith
  have hfac : ((a : ℝ) / Real.exp 1) ^ a ≤ (a.factorial : ℝ) := by
    calc
      ((a : ℝ) / Real.exp 1) ^ a
          ≤ Real.sqrt (2 * Real.pi * a) * ((a : ℝ) / Real.exp 1) ^ a := by
            exact le_mul_of_one_le_left (by positivity) hsqrt
      _ ≤ (a.factorial : ℝ) := Stirling.le_factorial_stirling a
  have hchoose : ((Nat.choose (n + a) a : ℕ) : ℝ) ≤
      (((n + a : ℕ) : ℝ) ^ a) / (a.factorial : ℝ) := by
    exact Nat.choose_le_pow_div a (n + a)
  have hfacpos : (0 : ℝ) < (a.factorial : ℝ) := by positivity
  have hbasepos : (0 : ℝ) < (a : ℝ) / Real.exp 1 := by positivity
  calc
    ((Nat.choose (n + a) a : ℕ) : ℝ)
        ≤ (((n + a : ℕ) : ℝ) ^ a) / (a.factorial : ℝ) := hchoose
    _ ≤ (((n + a : ℕ) : ℝ) ^ a) /
          (((a : ℝ) / Real.exp 1) ^ a) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ = (((n + a : ℕ) : ℝ) / ((a : ℝ) / Real.exp 1)) ^ a := by
      exact (div_pow _ _ a).symm
    _ = (Real.exp 1 * ((n + a : ℕ) : ℝ) / (a : ℝ)) ^ a := by
      congr 1
      field_simp [ne_of_gt haR, Real.exp_ne_zero]

/-- With `a = ceil(2n/t)`, the cap binomial coefficient is bounded by
`t^(6n/t)`.  The hypotheses are exactly the eventual range used in the
source proof. -/
theorem choose_add_pzCapSize_le_envelope
    (n t : ℕ) (hn : 0 < n) (ht : 3 ≤ t) (htn : t ≤ n) :
    ((Nat.choose (n + pzCapSize n t) (pzCapSize n t) : ℕ) : ℝ) ≤
      (t : ℝ) ^ ((6 : ℝ) * n / t) := by
  let a := pzCapSize n t
  have ht0 : 0 < t := by omega
  have ha0 : 0 < a := pzCapSize_pos hn ht0
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have htnR : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast htn
  have halower : (2 : ℝ) * n / t ≤ (a : ℝ) := by
    simpa [a] using pzCapSize_lower (n := n) ht0
  have haupper : (a : ℝ) < (2 : ℝ) * n / t + 1 := by
    simpa [a] using pzCapSize_upper (n := n) ht0
  have hratio : ((n + a : ℕ) : ℝ) / (a : ℝ) ≤ (t : ℝ) := by
    rw [Nat.cast_add]
    have hna : (n : ℝ) / (a : ℝ) ≤ (t : ℝ) / 2 := by
      rw [div_le_iff₀ haR]
      have htwo : (2 : ℝ) * n ≤ (a : ℝ) * t :=
        (div_le_iff₀ htR).mp halower
      nlinarith
    rw [add_div, div_self (ne_of_gt haR)]
    have ht2 : (1 : ℝ) ≤ (t : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      exact_mod_cast (show 2 ≤ t by omega)
    linarith
  have hexpt : Real.exp 1 ≤ (t : ℝ) :=
    Real.exp_one_lt_three.le.trans (by exact_mod_cast ht)
  have hbase : Real.exp 1 * ((n + a : ℕ) : ℝ) / (a : ℝ) ≤ (t : ℝ) ^ 2 := by
    rw [mul_div_assoc]
    exact (mul_le_mul hexpt hratio (by positivity) (by positivity)).trans_eq (by ring)
  have haexp : (a : ℝ) ≤ (3 : ℝ) * n / t := by
    have hone : (1 : ℝ) ≤ (n : ℝ) / t := by
      rw [le_div_iff₀ htR]
      simpa using htnR
    refine haupper.le.trans ?_
    calc
      (2 : ℝ) * n / t + 1 = 2 * ((n : ℝ) / t) + 1 := by ring
      _ ≤ 2 * ((n : ℝ) / t) + (n : ℝ) / t := by linarith
      _ = (3 : ℝ) * n / t := by ring
  have hchoose := choose_add_le_exp_mul_div_pow n a ha0
  calc
    ((Nat.choose (n + pzCapSize n t) (pzCapSize n t) : ℕ) : ℝ)
        = ((Nat.choose (n + a) a : ℕ) : ℝ) := rfl
    _ ≤ (Real.exp 1 * ((n + a : ℕ) : ℝ) / (a : ℝ)) ^ a := hchoose
    _ ≤ ((t : ℝ) ^ 2) ^ a := by
      exact pow_le_pow_left₀ (by positivity) hbase _
    _ = (t : ℝ) ^ (2 * a : ℕ) := (pow_mul _ 2 a).symm
    _ = (t : ℝ) ^ ((2 : ℝ) * a) := by
      rw [← Real.rpow_natCast]
      norm_num
    _ ≤ (t : ℝ) ^ ((6 : ℝ) * n / t) := by
      apply Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ t by omega))
      calc
        (2 : ℝ) * a ≤ 2 * ((3 : ℝ) * n / t) :=
          mul_le_mul_of_nonneg_left haexp (by norm_num)
        _ = (6 : ℝ) * n / t := by ring

/-- The sixth power appearing after the two square-root/Dilworth losses is
bounded by the source envelope with the explicit constant `36`. -/
theorem choose_add_pzCapSize_pow_six_le_envelope
    (n t : ℕ) (hn : 0 < n) (ht : 3 ≤ t) (htn : t ≤ n) :
    ((Nat.choose (n + pzCapSize n t) (pzCapSize n t) : ℕ) : ℝ) ^ 6 ≤
      (t : ℝ) ^ ((36 : ℝ) * n / t) := by
  have h := choose_add_pzCapSize_le_envelope n t hn ht htn
  calc
    ((Nat.choose (n + pzCapSize n t) (pzCapSize n t) : ℕ) : ℝ) ^ 6
        ≤ ((t : ℝ) ^ ((6 : ℝ) * n / t)) ^ (6 : ℕ) :=
          pow_le_pow_left₀ (by positivity) h 6
    _ = (t : ℝ) ^ ((36 : ℝ) * n / t) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      ring

end

end Erdos651
