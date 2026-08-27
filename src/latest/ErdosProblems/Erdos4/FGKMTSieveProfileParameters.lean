import ErdosProblems.Erdos4.FGKMTMomentBudget
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! An explicit profile family with polynomial size and logarithmic gain. -/

namespace Erdos4.FGKMT

def sieveDimension (j : ℕ) : ℕ := 2 ^ j

noncomputable def sieveProfileScale (j : ℕ) : ℝ := 128 * (j : ℝ) * (sieveDimension j : ℝ)

theorem sieveDimension_pos (j : ℕ) : 0 < sieveDimension j := by unfold sieveDimension; positivity

theorem large_dimension_dominates_linear {j : ℕ} (hj : 16 ≤ j) :
    128 * j + 1 < sieveDimension j := by
  unfold sieveDimension
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
      rw [pow_succ]
      have hstep : 128 * (j + 1) + 1 < (128 * j + 1) * 2 := by omega
      exact hstep.trans (Nat.mul_lt_mul_of_pos_right ih (by norm_num))

theorem sieveProfileScale_ge_one {j : ℕ} (hj : 1 ≤ j) : 1 ≤ sieveProfileScale j := by
  have hk : (1 : ℝ) ≤ sieveDimension j := by exact_mod_cast sieveDimension_pos j
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  unfold sieveProfileScale
  nlinarith

theorem sieveProfileScale_le_square {j : ℕ} (hj : 16 ≤ j) :
    1 + sieveProfileScale j ≤ (sieveDimension j : ℝ) ^ 2 := by
  have hlin : 128 * (j : ℝ) + 1 ≤ sieveDimension j := by
    exact_mod_cast (large_dimension_dominates_linear hj).le
  have hk : (1 : ℝ) ≤ sieveDimension j := by exact_mod_cast sieveDimension_pos j
  have hmul := mul_le_mul_of_nonneg_right hlin (by positivity : (0 : ℝ) ≤ sieveDimension j)
  unfold sieveProfileScale
  nlinarith

theorem log_sieveDimension (j : ℕ) : Real.log (sieveDimension j : ℝ) = (j : ℝ) * Real.log 2 := by
  unfold sieveDimension
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem sieveProfileScale_log_le {j : ℕ} (hj : 16 ≤ j) :
    Real.log (1 + sieveProfileScale j) ≤ 2 * (j : ℝ) := by
  have hz : 0 < 1 + sieveProfileScale j := by
    have hh := sieveProfileScale_ge_one (by omega : 1 ≤ j)
    linarith
  have hh := Real.log_le_log hz (sieveProfileScale_le_square hj)
  rw [Real.log_pow, log_sieveDimension] at hh
  have hlog2 : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hmul := mul_le_mul_of_nonneg_left hlog2 hj0
  norm_num only [Nat.cast_ofNat] at hh
  nlinarith

theorem sieveProfileScale_moment_budget {j : ℕ} (hj : 16 ≤ j) :
    32 * (sieveDimension j : ℝ) * (Real.log (1 + sieveProfileScale j) + 1) ≤
      sieveProfileScale j := by
  have hh := sieveProfileScale_log_le hj
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  have hlog : Real.log (1 + sieveProfileScale j) + 1 ≤ 4 * (j : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 32 * (sieveDimension j : ℝ))
  exact hmul.trans_eq (by unfold sieveProfileScale; ring)

theorem sieveProfileScale_short_log_lower {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) * Real.log 2 ≤ Real.log (1 + sieveProfileScale j / 2) := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hk : (0 : ℝ) < sieveDimension j := by exact_mod_cast sieveDimension_pos j
  have harg : (sieveDimension j : ℝ) ≤ 1 + sieveProfileScale j / 2 := by
    unfold sieveProfileScale
    nlinarith
  rw [← log_sieveDimension]
  exact Real.log_le_log hk harg

end Erdos4.FGKMT
