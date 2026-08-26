/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The noise parameter has slope one half at zero logarithmic spacing.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LogGaussianParameters

namespace Erdos521

open Filter
open scoped Topology

theorem logScaleNoise_zero : logScaleNoise 0 = 0 := by simp [logScaleNoise]

theorem logScaleNoise_hasDerivAt_zero : HasDerivAt logScaleNoise (1 / 2) 0 := by
  have hnum : HasDerivAt (fun δ : ℝ ↦ Real.exp δ - 1) 1 0 := by
    simpa only [Real.exp_zero] using (Real.hasDerivAt_exp 0).sub_const 1
  have hhalf : HasDerivAt (fun δ : ℝ ↦ Real.exp (δ / 2)) (1 / 2) 0 := by
    simpa only [zero_div, Real.exp_zero, one_mul, Function.comp_def, id_eq] using
      (Real.hasDerivAt_exp (0 / 2)).comp 0 ((hasDerivAt_id (0 : ℝ)).div_const 2)
  have hden := hhalf.const_mul 2
  have h := hnum.div hden (by norm_num : (2 : ℝ) * Real.exp (0 / 2) ≠ 0)
  convert h using 1 <;> first | rfl | norm_num

theorem logScaleNoise_slope :
    Tendsto (fun δ : ℝ ↦ logScaleNoise δ / δ) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  simpa only [zero_add, logScaleNoise_zero, sub_zero, smul_eq_mul, div_eq_inv_mul] using
    logScaleNoise_hasDerivAt_zero.tendsto_slope_zero_right

theorem logScaleNoise_tendsto_right : Tendsto logScaleNoise (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto logScaleNoise (𝓝[>] 0) (𝓝 (logScaleNoise 0)) :=
      logScaleNoise_hasDerivAt_zero.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [logScaleNoise_zero] using h
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact logScaleNoise_pos hδ

end Erdos521
