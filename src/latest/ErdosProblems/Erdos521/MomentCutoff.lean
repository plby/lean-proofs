/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Logarithmic cutoffs absorb the finite-degree remainder in local moments.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LocalTailDecay

namespace Erdos521

open Filter
open scoped Topology

noncomputable def localMomentSlope (p : ℕ) : ℝ := ((p : ℝ) + 1) / localTailRate

noncomputable def localMomentCutoff (p n : ℕ) : ℕ := ⌈localMomentSlope p * Real.log n⌉₊

theorem localMomentSlope_pos (p : ℕ) : 0 < localMomentSlope p :=
  div_pos (by positivity) localTailRate_pos

theorem localMomentSlope_mul_rate (p : ℕ) : localTailRate * localMomentSlope p = (p : ℝ) + 1 := by
  unfold localMomentSlope
  field_simp [localTailRate_pos.ne']

theorem eventually_localMomentCutoff_large (p : ℕ) :
    ∀ᶠ n : ℕ in atTop, 8 ≤ localMomentCutoff p n := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hscale := hlog.const_mul_atTop (localMomentSlope_pos p)
  filter_upwards [hscale.eventually_ge_atTop 8] with n hn
  have h := hn.trans (Nat.le_ceil (localMomentSlope p * Real.log n))
  exact_mod_cast h

theorem localMomentCutoff_gap (p n : ℕ) (hlog : 1 ≤ Real.log n) :
    32 * (localMomentCutoff p n : ℝ) ≤ 32 * (localMomentSlope p + 1) * Real.log n := by
  have hceil := Nat.ceil_lt_add_one (mul_nonneg (localMomentSlope_pos p).le (by linarith : 0 ≤ Real.log n))
  change (localMomentCutoff p n : ℝ) < localMomentSlope p * Real.log n + 1 at hceil
  nlinarith

theorem localMomentCutoff_remainder (p n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ p * Real.exp (-localTailRate * localMomentCutoff p n) ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hceil := Nat.le_ceil (localMomentSlope p * Real.log n)
  change localMomentSlope p * Real.log n ≤ (localMomentCutoff p n : ℝ) at hceil
  have hmul := mul_le_mul_of_nonneg_left hceil localTailRate_pos.le
  rw [← mul_assoc, localMomentSlope_mul_rate] at hmul
  have hexp : Real.exp (-localTailRate * localMomentCutoff p n) ≤ Real.exp (-(p : ℝ) * Real.log n) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    (n : ℝ) ^ p * Real.exp (-localTailRate * localMomentCutoff p n) ≤
        (n : ℝ) ^ p * Real.exp (-(p : ℝ) * Real.log n) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 1 := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn₀]
      exact mul_inv_cancel₀ (pow_ne_zero _ hn₀.ne')

end Erdos521
