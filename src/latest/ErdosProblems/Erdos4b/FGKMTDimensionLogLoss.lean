/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSqrtLogGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Explicit logarithmic losses in the growing-dimensional prime error

The natural base-two logarithm and the Cauchy power are bounded on one
positive log-log scale, with every dimension and radius still free.
-/

namespace Erdos4b.FGKMT

noncomputable section

def dimensionLogLossScale (x : ℕ) : ℝ := 1 + Real.log (1 + Real.log (x : ℝ))

theorem one_le_dimensionLogLossScale (x : ℕ) : 1 ≤ dimensionLogLossScale x := by
  have hlog := Real.log_natCast_nonneg x
  have h := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + Real.log (x : ℝ))
  dsimp [dimensionLogLossScale]
  linarith

theorem natLog_two_le_two_log (R : ℕ) :
    (Nat.log 2 R : ℝ) ≤ 2 * Real.log (R : ℝ) := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog0 := Real.log_natCast_nonneg R
  calc
    _ ≤ Real.log (R : ℝ) / Real.log 2 := by
      simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb R 2
    _ ≤ _ := (div_le_iff₀ (Real.log_pos one_lt_two)).mpr (by nlinarith)

theorem one_add_log_natLog_le_dimensionScale {R x : ℕ} (hR : 2 ≤ R) (hRx : R ≤ x) :
    1 + Real.log (Nat.log 2 R : ℕ) ≤ 2 * dimensionLogLossScale x := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hNpos : (0 : ℝ) < (Nat.log 2 R : ℕ) := by
    exact_mod_cast Nat.log_pos (by norm_num : 1 < 2) hR
  have hlogRx : Real.log (R : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log hRpos (by exact_mod_cast hRx)
  have hN := (natLog_two_le_two_log R).trans (mul_le_mul_of_nonneg_left hlogRx (by norm_num))
  have harg : (Nat.log 2 R : ℝ) ≤ (1 + Real.log (x : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (x : ℝ))]
  have hlog : Real.log (Nat.log 2 R : ℕ) ≤ 2 * Real.log (1 + Real.log (x : ℝ)) := by
    calc
      _ ≤ Real.log ((1 + Real.log (x : ℝ)) ^ 2) := Real.log_le_log hNpos harg
      _ = _ := by rw [Real.log_pow]; norm_num
  dsimp [dimensionLogLossScale]
  linarith

theorem log_cauchyRadius_le_dimensionScale {R x : ℕ} (hR : 1 ≤ R) (hRx : R ≤ x) :
    Real.log (1 + Real.log (R ^ 2 : ℕ)) ≤ 2 * dimensionLogLossScale x := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hFpos : 0 < 1 + Real.log (R ^ 2 : ℕ) := by positivity
  have hlogRx : Real.log (R : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log hRpos (by exact_mod_cast hRx)
  have hlogR2 : Real.log (R ^ 2 : ℕ) = 2 * Real.log (R : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have harg : 1 + Real.log (R ^ 2 : ℕ) ≤ (1 + Real.log (x : ℝ)) ^ 2 := by
    rw [hlogR2]
    nlinarith [sq_nonneg (Real.log (x : ℝ))]
  have hlog := Real.log_le_log hFpos harg
  rw [Real.log_pow] at hlog
  dsimp [dimensionLogLossScale]
  norm_num at hlog
  rw [hlogR2]
  linarith

theorem cauchyRadius_pow_le_exp {m R x : ℕ} (hR : 1 ≤ R) (hRx : R ≤ x) :
    (1 + Real.log (R ^ 2 : ℕ)) ^ ((3 * m) ^ 2) ≤
      Real.exp (18 * (m + 1 : ℕ) ^ 2 * dimensionLogLossScale x) := by
  let F : ℝ := 1 + Real.log (R ^ 2 : ℕ)
  let N := (3 * m) ^ 2
  have hF : 0 < F := by dsimp [F]; positivity
  have hN : (N : ℝ) ≤ 9 * (m + 1 : ℕ) ^ 2 := by
    dsimp [N]
    push_cast
    nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have hS : 0 ≤ dimensionLogLossScale x := zero_le_one.trans (one_le_dimensionLogLossScale x)
  calc
    _ = Real.exp ((N : ℝ) * Real.log F) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hF N)]
    _ ≤ Real.exp ((N : ℝ) * (2 * dimensionLogLossScale x)) :=
      Real.exp_monotone (mul_le_mul_of_nonneg_left
        (log_cauchyRadius_le_dimensionScale hR hRx) (Nat.cast_nonneg N))
    _ ≤ Real.exp ((9 * (m + 1 : ℕ) ^ 2) * (2 * dimensionLogLossScale x)) :=
      Real.exp_monotone (mul_le_mul_of_nonneg_right hN (by positivity))
    _ = _ := by congr 1; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.one_add_log_natLog_le_dimensionScale
#print axioms Erdos4b.FGKMT.cauchyRadius_pow_le_exp
