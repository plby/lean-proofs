/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceSurvivalBudget

/-! # Explicit logarithmic bounds for the source covering parameters -/

namespace Erdos4b.FGKMT

noncomputable section

def sourceCoveringSize (k : ℕ) (x : ℝ) : ℕ := 2 * k * sourceBatchCount x + 1

theorem sourceSurvivalFloor_neg_log (x : ℝ) :
    -Real.log (sourceSurvivalFloor x) =
      Real.log 2 + (sourceBatchCount x : ℝ) * Real.log 5 := by
  rw [sourceSurvivalFloor,
    Real.log_div (geometricSurvival_pos _).ne' (by norm_num),
    geometricSurvival, Real.log_pow, Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

theorem sourceSurvivalFloor_neg_log_le {x : ℝ} (hℓ : 1 ≤ Real.log (Real.log x)) :
    -Real.log (sourceSurvivalFloor x) ≤ 2 * Real.log (Real.log x) := by
  have hp := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 5) (sourceBatchCount x))
    (sourceBatchCount_pow_le hℓ)
  rw [Real.log_pow] at hp
  rw [sourceSurvivalFloor_neg_log]
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.log_le_self (zero_le_one.trans hℓ)]

theorem sourceBatchCount_ten_pow_le {x : ℝ} (hℓ : 1 ≤ Real.log (Real.log x)) :
    (10 : ℝ) ^ (sourceBatchCount x + 2) ≤ 100 * Real.log (Real.log x) ^ 2 := by
  have hpow : (10 : ℝ) ^ sourceBatchCount x ≤ ((5 : ℝ) ^ sourceBatchCount x) ^ 2 := by
    calc
      _ ≤ (25 : ℝ) ^ sourceBatchCount x := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = _ := by
        rw [show (25 : ℝ) = 5 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm, pow_mul]
  have hsquare := pow_le_pow_left₀ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5) _)
    (sourceBatchCount_pow_le hℓ) 2
  calc
    _ = 100 * (10 : ℝ) ^ sourceBatchCount x := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hpow.trans hsquare) (by norm_num)

theorem sourceCoveringSize_le {k : ℕ} {x : ℝ} (hL : 1 ≤ Real.log x)
    (hℓ : 1 ≤ Real.log (Real.log x)) (hk : (k : ℝ) ≤ Real.log x ^ (1 / 10 : ℝ)) :
    (sourceCoveringSize k x : ℝ) ≤
      3 * Real.log x ^ (1 / 10 : ℝ) * Real.log (Real.log x) := by
  have hu : 1 ≤ Real.log x ^ (1 / 10 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hm : (sourceBatchCount x : ℝ) ≤ Real.log (Real.log x) :=
    (sourceBatchCount_le_logloglog hℓ).trans (Real.log_le_self (zero_le_one.trans hℓ))
  have hkm := mul_le_mul hk hm (Nat.cast_nonneg _) (by linarith :
    0 ≤ Real.log x ^ (1 / 10 : ℝ))
  have hprod : 1 ≤ Real.log x ^ (1 / 10 : ℝ) * Real.log (Real.log x) := by nlinarith
  simp only [sourceCoveringSize, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  nlinarith

theorem coveringScale_log (A : ℕ) (D : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Real.log (coveringScale A D κ) = Real.log 256 + (A : ℝ) * D - (A : ℝ) * Real.log κ := by
  rw [coveringScale, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_div (by norm_num) (pow_ne_zero A hκ.ne'), Real.log_one, Real.log_pow]
  ring

theorem log_256_le_eight : Real.log 256 ≤ 8 := by
  rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem sourceCoveringScale_log_le {k : ℕ} {x : ℝ} (hL : 1 ≤ Real.log x)
    (hℓ : 1 ≤ Real.log (Real.log x)) (hk : (k : ℝ) ≤ Real.log x ^ (1 / 10 : ℝ)) :
    Real.log (coveringScale (sourceCoveringSize k x) 4 (sourceSurvivalFloor x)) ≤
      26 * Real.log x ^ (1 / 10 : ℝ) * Real.log (Real.log x) ^ 2 := by
  let u := Real.log x ^ (1 / 10 : ℝ)
  let ℓ := Real.log (Real.log x)
  let A := sourceCoveringSize k x
  have hu : 1 ≤ u := Real.one_le_rpow hL (by norm_num)
  have hA : (A : ℝ) ≤ 3 * u * ℓ := sourceCoveringSize_le hL hℓ hk
  have hlog : 4 - Real.log (sourceSurvivalFloor x) ≤ 6 * ℓ := by
    have h := sourceSurvivalFloor_neg_log_le hℓ
    change -Real.log (sourceSurvivalFloor x) ≤ 2 * ℓ at h
    linarith
  have hℓsq : 1 ≤ ℓ ^ 2 := by nlinarith
  have hbase : 1 ≤ u * ℓ ^ 2 := by nlinarith
  calc
    _ = Real.log 256 + (A : ℝ) * (4 - Real.log (sourceSurvivalFloor x)) := by
      rw [coveringScale_log _ _ (sourceSurvivalFloor_pos x)]
      ring
    _ ≤ 8 + (A : ℝ) * (6 * ℓ) :=
      add_le_add log_256_le_eight (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
    _ ≤ 8 + (3 * u * ℓ) * (6 * ℓ) := by gcongr
    _ = 8 + 18 * u * ℓ ^ 2 := by ring
    _ ≤ _ := by change 8 + 18 * u * ℓ ^ 2 ≤ 26 * u * ℓ ^ 2; nlinarith

theorem sourceCovering_log_budget_le {k : ℕ} {x : ℝ} (hL : 1 ≤ Real.log x)
    (hℓ : 1 ≤ Real.log (Real.log x)) (hk : (k : ℝ) ≤ Real.log x ^ (1 / 10 : ℝ)) :
    (10 : ℝ) ^ (sourceBatchCount x + 2) *
      Real.log (coveringScale (sourceCoveringSize k x) 4 (sourceSurvivalFloor x)) ≤
        2600 * Real.log x ^ (1 / 10 : ℝ) * Real.log (Real.log x) ^ 4 := by
  calc
    _ ≤ (10 : ℝ) ^ (sourceBatchCount x + 2) *
        (26 * Real.log x ^ (1 / 10 : ℝ) * Real.log (Real.log x) ^ 2) :=
      mul_le_mul_of_nonneg_left (sourceCoveringScale_log_le hL hℓ hk) (by positivity)
    _ ≤ (100 * Real.log (Real.log x) ^ 2) *
        (26 * Real.log x ^ (1 / 10 : ℝ) * Real.log (Real.log x) ^ 2) :=
      mul_le_mul_of_nonneg_right (sourceBatchCount_ten_pow_le hℓ) (by positivity)
    _ = _ := by ring

end

end Erdos4b.FGKMT
