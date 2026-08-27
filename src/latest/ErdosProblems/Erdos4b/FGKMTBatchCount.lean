/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTGeometricBatchWeights

/-! # Exact floor and geometric bounds for the number of source batches -/

namespace Erdos4b.FGKMT

noncomputable section

def sourceBatchCount (x : ℝ) : ℕ :=
  ⌊Real.log (Real.log (Real.log x)) / Real.log 5⌋₊

theorem one_le_log_five : (1 : ℝ) ≤ Real.log 5 := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 5)).mpr
  exact Real.exp_one_lt_three.le.trans (by norm_num)

theorem sourceBatchCount_pow_le {x : ℝ} (hℓ : 1 ≤ Real.log (Real.log x)) :
    (5 : ℝ) ^ sourceBatchCount x ≤ Real.log (Real.log x) := by
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hℓ0 : 0 < Real.log (Real.log x) := zero_lt_one.trans_le hℓ
  have hm : (sourceBatchCount x : ℝ) ≤
      Real.log (Real.log (Real.log x)) / Real.log 5 :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hℓ) h5.le)
  have h := Real.exp_le_exp.mpr ((le_div_iff₀ h5).mp hm)
  simpa only [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5),
    Real.exp_log hℓ0] using h

theorem loglog_lt_sourceBatchCount_succ_pow {x : ℝ}
    (hℓ : 1 ≤ Real.log (Real.log x)) :
    Real.log (Real.log x) < (5 : ℝ) ^ (sourceBatchCount x + 1) := by
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hm : Real.log (Real.log (Real.log x)) / Real.log 5 <
      (sourceBatchCount x : ℝ) + 1 := Nat.lt_floor_add_one _
  have h := Real.exp_lt_exp.mpr ((div_lt_iff₀ h5).mp hm)
  have hℓ0 : 0 < Real.log (Real.log x) := zero_lt_one.trans_le hℓ
  simpa only [← Nat.cast_add_one, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 5), Real.exp_log hℓ0] using h

theorem sourceBatchCount_le_endpoint {x : ℝ} (hx : 1 ≤ x)
    (hL : 1 ≤ Real.log x) (hℓ : 1 ≤ Real.log (Real.log x)) :
    (sourceBatchCount x : ℝ) ≤ x := by
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hlogℓ : 0 ≤ Real.log (Real.log (Real.log x)) := Real.log_nonneg hℓ
  calc
    _ ≤ Real.log (Real.log (Real.log x)) / Real.log 5 :=
      Nat.floor_le (div_nonneg hlogℓ h5.le)
    _ ≤ Real.log (Real.log (Real.log x)) := by
      exact div_le_self hlogℓ one_le_log_five
    _ ≤ Real.log (Real.log x) := Real.log_le_self (zero_le_one.trans hℓ)
    _ ≤ Real.log x := Real.log_le_self (zero_le_one.trans hL)
    _ ≤ x := Real.log_le_self (zero_le_one.trans hx)

theorem geometricBatchTarget_lower {x : ℝ} (hℓ : 1 ≤ Real.log (Real.log x))
    {j : ℕ} (hj : j < sourceBatchCount x) :
    Real.log 5 / Real.log (Real.log x) ≤ geometricBatchTarget j := by
  have hpow : (5 : ℝ) ^ j ≤ Real.log (Real.log x) :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5) (Nat.le_of_lt hj)).trans
      (sourceBatchCount_pow_le hℓ)
  have hinv := one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 5) j) hpow
  calc
    _ = (1 / Real.log (Real.log x)) * Real.log 5 := by ring
    _ ≤ (1 / (5 : ℝ) ^ j) * Real.log 5 :=
      mul_le_mul_of_nonneg_right hinv (Real.log_nonneg (by norm_num))
    _ = geometricBatchTarget j := by rw [geometricBatchTarget, one_div_pow]

theorem geometricBatchTarget_ge_twice_tolerance {x : ℝ}
    (hℓ : 2 ≤ Real.log (Real.log x)) {j : ℕ} (hj : j < sourceBatchCount x) :
    2 * (1 / Real.log (Real.log x) ^ 2) ≤ geometricBatchTarget j := by
  have hℓ0 : 0 < Real.log (Real.log x) := by linarith
  apply le_trans _ (geometricBatchTarget_lower (by linarith) hj)
  apply (le_div_iff₀ hℓ0).mpr
  have hprod : (2 * (1 / Real.log (Real.log x) ^ 2)) * Real.log (Real.log x) =
      2 / Real.log (Real.log x) := by field_simp
  rw [hprod]
  exact ((div_le_one hℓ0).mpr hℓ).trans one_le_log_five

end

end Erdos4b.FGKMT
