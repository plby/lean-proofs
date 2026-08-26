/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.RankinMonotonicity
import ErdosProblems.Erdos4b.SourceDyadicScales

/-!
# Explicit iterated-logarithm bounds at the dyadic index endpoint

The prospective index has logarithm at most 3X. These estimates retain
the two powers of its third logarithm, which cannot be discarded.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

theorem rankin_log_two_le_one : Real.log 2 ≤ (1 : ℝ) := by
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem dyadicAmbientScale_expand (a r : ℕ) :
    dyadicAmbientScale a r = (2 : ℝ) ^ (a + 2 * r) * core r * Real.log 2 := by
  rw [dyadicAmbientScale_eq]
  simp only [primaryExponent, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem core_le_dyadicAmbientScale {a r : ℕ} (hr : 1 ≤ r) :
    (core r : ℝ) ≤ dyadicAmbientScale a r := by
  have he : (2 : ℝ) ≤ (2 : ℝ) ^ (a + 2 * r) := by
    have hh := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
      (show 1 ≤ a + 2 * r by omega)
    exact_mod_cast hh
  have hcoef : 1 ≤ (2 : ℝ) ^ (a + 2 * r) * Real.log 2 := by
    nlinarith [half_le_log_two]
  rw [dyadicAmbientScale_expand]
  have hh := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (core r) : (0 : ℝ) ≤ core r)
  nlinarith [hh]

theorem log_dyadicAmbientScale (a r : ℕ) :
    Real.log (dyadicAmbientScale a r) =
      ((a : ℝ) + 2 * r + (2 : ℝ) ^ r) * Real.log 2 + Real.log (Real.log 2) := by
  have hcore : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  rw [dyadicAmbientScale_expand,
    Real.log_mul (by positivity) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne',
    Real.log_mul (by positivity) (by exact_mod_cast (core_pos r).ne'), Real.log_pow, log_core]
  push_cast
  ring

def dyadicIndexLog (a r : ℕ) : ℝ := Real.log (3 * (primaryFrontier a r : ℝ))

theorem dyadicIndexLog_eq (a r : ℕ) :
    dyadicIndexLog a r = Real.log 3 + dyadicAmbientScale a r := by
  unfold dyadicIndexLog dyadicAmbientScale
  rw [Real.log_mul (by norm_num) (by exact_mod_cast (primaryFrontier_pos a r).ne')]

theorem dyadicIndexLog_bounds {a r : ℕ} (hr : 1 ≤ r) :
    dyadicAmbientScale a r ≤ dyadicIndexLog a r ∧
      dyadicIndexLog a r ≤ 2 * dyadicAmbientScale a r := by
  have hc2 : (2 : ℝ) ≤ core r := by exact_mod_cast two_le_dyadicCore r
  have hV : 2 ≤ dyadicAmbientScale a r := hc2.trans (core_le_dyadicAmbientScale hr)
  have hthree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hthree' : Real.log 3 ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  rw [dyadicIndexLog_eq]
  constructor <;> linarith

theorem dyadicIndexLog_pos {a r : ℕ} (hr : 1 ≤ r) : 0 < dyadicIndexLog a r :=
  lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) (one_le_dyadicAmbientScale a r))
    (dyadicIndexLog_bounds hr).1

theorem log_dyadicIndexLog_lower {a r : ℕ} (hr : 1 ≤ r) :
    (2 : ℝ) ^ r / 4 ≤ Real.log (dyadicIndexLog a r) := by
  have hcore : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hh := Real.log_le_log hcore
    ((core_le_dyadicAmbientScale (a := a) hr).trans (dyadicIndexLog_bounds hr).1)
  rw [log_core] at hh
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ r := by positivity
  nlinarith [mul_le_mul_of_nonneg_left half_le_log_two hp]

theorem log_dyadicIndexLog_upper {a r : ℕ} (hr : 4 ≤ r) (ha : a + 1 ≤ r) :
    Real.log (dyadicIndexLog a r) ≤ 4 * (2 : ℝ) ^ r := by
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hh := Real.log_le_log (dyadicIndexLog_pos (by omega : 1 ≤ r))
    (dyadicIndexLog_bounds (a := a) (by omega : 1 ≤ r)).2
  rw [Real.log_mul (by norm_num) hV.ne', log_dyadicAmbientScale] at hh
  have hloglog : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le rankin_log_two_le_one
  have hpow : (a : ℝ) + 2 * r + 1 ≤ (2 : ℝ) ^ r := by
    have hn : a + 2 * r + 1 ≤ 2 ^ r :=
      (show a + 2 * r + 1 ≤ 3 * r by omega).trans (three_mul_le_two_pow hr)
    exact_mod_cast hn
  have hcoeff : 0 ≤ (a : ℝ) + 2 * r + (2 : ℝ) ^ r + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left rankin_log_two_le_one hcoeff
  nlinarith [hmul, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r]

theorem loglog_dyadicIndexLog_upper {a r : ℕ} (hr : 4 ≤ r) (ha : a + 1 ≤ r) :
    Real.log (Real.log (dyadicIndexLog a r)) ≤ 3 * r := by
  have hlog : 0 < Real.log (dyadicIndexLog a r) :=
    lt_of_lt_of_le (by positivity) (log_dyadicIndexLog_lower (by omega : 1 ≤ r))
  have hh := Real.log_le_log hlog (log_dyadicIndexLog_upper hr ha)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hfour] at hh
  have hrone : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  nlinarith [mul_le_mul_of_nonneg_left rankin_log_two_le_one (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

end

end Erdos4b.SmoothParameters
