import Arxiv.Arxiv2411_18291.AsymptoticNibbleParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Absorbing polynomial prefactors into a stretched exponential -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem polynomial_stretched_exp_tendsto (K : ℝ) (m : ℕ) {C α : ℝ}
    (hC : 0 < C) (hα : 0 < α) :
    Tendsto (fun n : ℕ => K * (n : ℝ) ^ m * Real.exp (-(C * (n : ℝ) ^ α)))
      atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((m : ℝ) / α) C hC).comp
    (tendsto_rpow_atTop hα)
  have hp : Tendsto (fun x : ℝ => x ^ m * Real.exp (-(C * x ^ α))) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp only [Function.comp_def]
    rw [← Real.rpow_mul hx.le, show α * ((m : ℝ) / α) = m by field_simp,
      Real.rpow_natCast, neg_mul]
  simpa only [Function.comp_def, mul_zero, mul_assoc] using
    (hp.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul K

theorem eventually_polynomial_mul_exp_lt_exp (K : ℝ) (m : ℕ) (hK : 0 ≤ K)
    {C α β : ℝ} (hC : 0 < C) (hα : 0 < α) (hβα : β < α) :
    ∀ᶠ n : ℕ in atTop,
      K * (n : ℝ) ^ m * Real.exp (-(C * (n : ℝ) ^ α)) <
        Real.exp (-((n : ℝ) ^ β)) := by
  have hhalf : 0 < C / 2 := by positivity
  filter_upwards [eventually_scaled_rpow_le 1 hhalf hβα,
    (polynomial_stretched_exp_tendsto K m hhalf hα).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hscale hsmall
  have hexp : Real.exp (-((C / 2) * (n : ℝ) ^ α)) ≤
      Real.exp (-((n : ℝ) ^ β)) := by
    apply Real.exp_le_exp.mpr
    linarith only [hscale]
  let A := K * (n : ℝ) ^ m
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  calc
    _ = (A * Real.exp (-((C / 2) * (n : ℝ) ^ α))) *
        Real.exp (-((C / 2) * (n : ℝ) ^ α)) := by
      rw [mul_assoc A, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (A * Real.exp (-((C / 2) * (n : ℝ) ^ α))) *
        Real.exp (-((n : ℝ) ^ β)) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hA (Real.exp_pos _).le)
    _ < 1 * Real.exp (-((n : ℝ) ^ β)) :=
      mul_lt_mul_of_pos_right hsmall (Real.exp_pos _)
    _ = _ := one_mul _

end Arxiv2411_18291
