/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherPageEnvelope
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Exponential growth of the normalized Gallagher Gamma factor

The factorial quotients in the normalized derivative term are central-binomial
ratios.  Bounding them by powers of two shows that the whole factor grows only
exponentially with the detector order (up to a quadratic factor).
-/

namespace Erdos48

open scoped BigOperators

lemma factorial_ratio_le_two_pow (k : ℕ) :
    (((2 * k).factorial : ℕ) : ℝ) /
        ((((k.factorial : ℕ) : ℝ) ^ 2)) ≤ (2 : ℝ) ^ (2 * k) := by
  have hidNat : (2 * k).choose k * k.factorial * k.factorial =
      (2 * k).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    have hsub : 2 * k - k = k := by omega
    simpa only [hsub] using h
  have hchoose : (((2 * k).choose k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
    exact_mod_cast Nat.choose_le_two_pow (2 * k) k
  have hfac : (0 : ℝ) < ((k.factorial : ℕ) : ℝ) := by positivity
  rw [← hidNat]
  push_cast
  field_simp
  nlinarith [sq_pos_of_pos hfac]

theorem normalizedGallagherDerivativeGammaCoefficient_le_growth
    {eta : ℝ} (_heta : 0 ≤ eta) (heta8 : eta ≤ 1 / 8)
    {J k : ℕ} (hkJ : k ≤ J) :
    normalizedGallagherDerivativeGammaCoefficient eta J k ≤
      (40 / Real.log 2) * (578 : ℝ) ^ (2 * J) *
        (16 : ℝ) ^ J * (J + 1 : ℕ) ^ 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hetaPow : (2 : ℝ) ^ (4 * eta) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show 4 * eta ≤ 1 by linarith)
    simpa using h
  have hratioK := factorial_ratio_le_two_pow k
  have hratioPred := factorial_ratio_le_two_pow (k - 1)
  have hfirstRatio :
      (((2 * (k - 1)).factorial : ℕ) : ℝ) /
          (((k.factorial : ℕ) : ℝ) ^ 2) ≤
        (2 : ℝ) ^ (2 * (k - 1)) := by
    have hfacNat : (k - 1).factorial ≤ k.factorial :=
      Nat.factorial_le (Nat.sub_le k 1)
    have hfac : (((k - 1).factorial : ℕ) : ℝ) ≤
        ((k.factorial : ℕ) : ℝ) := by exact_mod_cast hfacNat
    have hfacSq : ((((k - 1).factorial : ℕ) : ℝ) ^ 2) ≤
        (((k.factorial : ℕ) : ℝ) ^ 2) :=
      pow_le_pow_left₀ (by positivity) hfac 2
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hfacSq).trans hratioPred
  have hkpow : (2 : ℝ) ^ (4 * k) ≤ (16 : ℝ) ^ J := by
    calc
      (2 : ℝ) ^ (4 * k) ≤ (2 : ℝ) ^ (4 * J) :=
        pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 4 hkJ)
      _ = (16 : ℝ) ^ J := by norm_num [pow_mul]
  have hk1 : (k : ℝ) ≤ (J + 1 : ℕ) := by
    exact_mod_cast (hkJ.trans (by omega))
  have hkSq : (k : ℝ) ^ 2 ≤ ((J + 1 : ℕ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hk1 2
  have hpowPred :
      (2 : ℝ) ^ (2 * (k - 1)) * (2 : ℝ) ^ (2 * (k - 1)) ≤
        (2 : ℝ) ^ (4 * k) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hratioFirstFull :
      ((2 : ℝ) ^ (4 * eta) * (2 * (k - 1)).factorial) /
          (((k.factorial : ℕ) : ℝ) ^ 2) ≤
        2 * (2 : ℝ) ^ (2 * (k - 1)) := by
    calc
      ((2 : ℝ) ^ (4 * eta) * (2 * (k - 1)).factorial) /
          (((k.factorial : ℕ) : ℝ) ^ 2) =
        (2 : ℝ) ^ (4 * eta) *
          ((((2 * (k - 1)).factorial : ℕ) : ℝ) /
            (((k.factorial : ℕ) : ℝ) ^ 2)) := by ring
      _ ≤ 2 * (2 : ℝ) ^ (2 * (k - 1)) :=
        mul_le_mul hetaPow hfirstRatio (by positivity) (by positivity)
  have hratioFull :
      ((2 : ℝ) ^ (4 * eta) * (2 * k).factorial) /
          (((k.factorial : ℕ) : ℝ) ^ 2) ≤
        2 * (2 : ℝ) ^ (2 * k) := by
    calc
      ((2 : ℝ) ^ (4 * eta) * (2 * k).factorial) /
          (((k.factorial : ℕ) : ℝ) ^ 2) =
        (2 : ℝ) ^ (4 * eta) *
          ((((2 * k).factorial : ℕ) : ℝ) /
            (((k.factorial : ℕ) : ℝ) ^ 2)) := by ring
      _ ≤ 2 * (2 : ℝ) ^ (2 * k) :=
        mul_le_mul hetaPow hratioK (by positivity) (by positivity)
  unfold normalizedGallagherDerivativeGammaCoefficient
  have hinside :
      16 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (2 * (k - 1)) *
            ((2 : ℝ) ^ (4 * eta) * (2 * (k - 1)).factorial) /
              (((k.factorial : ℕ) : ℝ) ^ 2 * Real.log 2) +
        4 * (2 : ℝ) ^ (2 * k) *
            ((2 : ℝ) ^ (4 * eta) * (2 * k).factorial) /
              (((k.factorial : ℕ) : ℝ) ^ 2 * Real.log 2) ≤
        (40 / Real.log 2) * (J + 1 : ℕ) ^ 2 *
          (2 : ℝ) ^ (4 * k) := by
    have hfirst :
        16 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (2 * (k - 1)) *
            ((2 : ℝ) ^ (4 * eta) * (2 * (k - 1)).factorial) /
              (((k.factorial : ℕ) : ℝ) ^ 2 * Real.log 2) ≤
          (32 / Real.log 2) * (J + 1 : ℕ) ^ 2 *
            (2 : ℝ) ^ (4 * k) := by
      calc
        _ = (16 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (2 * (k - 1))) *
              (((2 : ℝ) ^ (4 * eta) * (2 * (k - 1)).factorial) /
                (((k.factorial : ℕ) : ℝ) ^ 2)) / Real.log 2 := by ring
        _ ≤ (16 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (2 * (k - 1))) *
              (2 * (2 : ℝ) ^ (2 * (k - 1))) / Real.log 2 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hratioFirstFull (by positivity)) hlog.le
        _ = (32 * (k : ℝ) ^ 2 *
              ((2 : ℝ) ^ (2 * (k - 1)) * (2 : ℝ) ^ (2 * (k - 1)))) /
                Real.log 2 := by ring
        _ ≤ (32 * ((J + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (4 * k)) /
              Real.log 2 := by
          apply div_le_div_of_nonneg_right _ hlog.le
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hkSq (by norm_num)) hpowPred
            (by positivity) (by positivity)
        _ = (32 / Real.log 2) * (J + 1 : ℕ) ^ 2 *
              (2 : ℝ) ^ (4 * k) := by ring
    have hsecond :
        4 * (2 : ℝ) ^ (2 * k) *
            ((2 : ℝ) ^ (4 * eta) * (2 * k).factorial) /
              (((k.factorial : ℕ) : ℝ) ^ 2 * Real.log 2) ≤
          (8 / Real.log 2) * (J + 1 : ℕ) ^ 2 *
            (2 : ℝ) ^ (4 * k) := by
      calc
        _ = (4 * (2 : ℝ) ^ (2 * k)) *
              (((2 : ℝ) ^ (4 * eta) * (2 * k).factorial) /
                (((k.factorial : ℕ) : ℝ) ^ 2)) / Real.log 2 := by ring
        _ ≤ (4 * (2 : ℝ) ^ (2 * k)) *
              (2 * (2 : ℝ) ^ (2 * k)) / Real.log 2 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hratioFull (by positivity)) hlog.le
        _ = (8 * ((2 : ℝ) ^ (2 * k) * (2 : ℝ) ^ (2 * k))) /
              Real.log 2 := by ring
        _ = (8 / Real.log 2) * (2 : ℝ) ^ (4 * k) := by
          rw [← pow_add, show 2 * k + 2 * k = 4 * k by omega]
          ring
        _ ≤ (8 / Real.log 2) * (J + 1 : ℕ) ^ 2 *
              (2 : ℝ) ^ (4 * k) := by
          have hJone : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) := by
            exact_mod_cast (show 1 ≤ J + 1 by omega)
          have hsquare : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) ^ 2 :=
            one_le_pow₀ hJone
          have hcoef : 0 ≤ 8 / Real.log 2 := by positivity
          exact mul_le_mul_of_nonneg_right
            (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsquare hcoef)
            (by positivity)
    calc
      _ ≤ (32 / Real.log 2) * (J + 1 : ℕ) ^ 2 * (2 : ℝ) ^ (4 * k) +
          (8 / Real.log 2) * (J + 1 : ℕ) ^ 2 * (2 : ℝ) ^ (4 * k) :=
        add_le_add hfirst hsecond
      _ = _ := by ring
  have houter : (((578 : ℝ) ^ J / 2) ^ 2) ≤ (578 : ℝ) ^ (2 * J) := by
    have hbase0 : (0 : ℝ) ≤ (578 : ℝ) ^ J := by positivity
    have hhalf : (578 : ℝ) ^ J / 2 ≤ (578 : ℝ) ^ J := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      nlinarith
    calc
      (((578 : ℝ) ^ J / 2) ^ 2) ≤ (((578 : ℝ) ^ J) ^ 2) := by
        exact pow_le_pow_left₀ (by positivity) hhalf 2
      _ = (578 : ℝ) ^ (2 * J) := by
        rw [← pow_mul]
        congr 1
        omega
  calc
    (((578 : ℝ) ^ J / 2) ^ 2) *
        (16 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (2 * (k - 1)) *
            ((2 : ℝ) ^ (4 * eta) * (2 * (k - 1)).factorial) /
              (((k.factorial : ℕ) : ℝ) ^ 2 * Real.log 2) +
          4 * (2 : ℝ) ^ (2 * k) *
            ((2 : ℝ) ^ (4 * eta) * (2 * k).factorial) /
              (((k.factorial : ℕ) : ℝ) ^ 2 * Real.log 2)) ≤
        (((578 : ℝ) ^ J / 2) ^ 2) *
          ((40 / Real.log 2) * (J + 1 : ℕ) ^ 2 *
            (2 : ℝ) ^ (4 * k)) := by gcongr
    _ ≤ (578 : ℝ) ^ (2 * J) *
        ((40 / Real.log 2) * (J + 1 : ℕ) ^ 2 * (16 : ℝ) ^ J) := by
      exact mul_le_mul houter
        (mul_le_mul_of_nonneg_left hkpow (by positivity)) (by positivity) (by positivity)
    _ = _ := by ring

end Erdos48
