import ErdosProblems.Erdos421.LogPowerWidthBounds

/-! # An explicit contour height for the prime-counting main term -/

namespace Erdos421

open Filter Topology

noncomputable def primeContourCoefficient : ℝ := ((2 : ℝ) ^ 44)⁻¹ / 64

noncomputable def primeContourHeight (x : ℝ) : ℝ := Real.exp ((Real.log x) ^ (1 / 4 : ℝ))

noncomputable def primeContourWidth (x : ℝ) : ℝ := logPowerZeroWidth (primeContourHeight x) / 64

theorem primeContourCoefficient_pos : 0 < primeContourCoefficient := by
  unfold primeContourCoefficient
  positivity

theorem primeContourHeight_pos (x : ℝ) : 0 < primeContourHeight x := Real.exp_pos _

theorem primeContourHeight_gt_one {x : ℝ} (hx : 1 < x) : 1 < primeContourHeight x :=
  Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos (Real.log_pos hx) _)

theorem primeContourHeight_tendsto : Tendsto primeContourHeight atTop atTop :=
  Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    Real.tendsto_log_atTop)

theorem primeContourWidth_pos {x : ℝ} (hx : 1 < x) : 0 < primeContourWidth x :=
  div_pos (logPowerZeroWidth_pos (primeContourHeight_gt_one hx)) (by norm_num)

theorem primeContourWidth_eq {x : ℝ} (hx : 1 < x) :
    primeContourWidth x = primeContourCoefficient / (Real.log x) ^ (15 / 64 : ℝ) := by
  unfold primeContourWidth primeContourHeight logPowerZeroWidth
  rw [Real.log_exp, ← Real.rpow_mul (Real.log_pos hx).le,
    show (1 / 4 : ℝ) * (15 / 16) = 15 / 64 by norm_num]
  unfold primeContourCoefficient
  ring

theorem primeContourWidth_log_identity {x : ℝ} (hx : 1 < x) :
    primeContourWidth x * Real.log x = primeContourCoefficient * (Real.log x) ^ (49 / 64 : ℝ) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  rw [primeContourWidth_eq hx]
  calc
    _ = primeContourCoefficient * (Real.log x / (Real.log x) ^ (15 / 64 : ℝ)) := by ring
    _ = primeContourCoefficient * ((Real.log x) ^ (1 : ℝ) / (Real.log x) ^ (15 / 64 : ℝ)) := by
      rw [Real.rpow_one]
    _ = primeContourCoefficient * (Real.log x) ^ ((1 : ℝ) - 15 / 64) := by
      rw [← Real.rpow_sub hL]
    _ = _ := by norm_num

theorem primeContourWidth_tendsto : Tendsto primeContourWidth atTop (𝓝 0) := by
  have h := (logPowerZeroWidth_tendsto_zero.comp primeContourHeight_tendsto).div_const (64 : ℝ)
  change Tendsto (fun x ↦ logPowerZeroWidth (primeContourHeight x) / 64) atTop (𝓝 0)
  simpa only [Function.comp_apply, zero_div] using h

theorem primeContourWidth_dominates_right_gap :
    ∀ᶠ x : ℝ in atTop, 1 / Real.log x ≤ primeContourWidth x := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 49 / 64)).comp Real.tendsto_log_atTop
  filter_upwards [hp.eventually (eventually_ge_atTop (1 / primeContourCoefficient)),
    eventually_ge_atTop (2 : ℝ)] with x hlarge hx
  have hx1 : 1 < x := by linarith
  have hc := (div_le_iff₀ primeContourCoefficient_pos).mp hlarge
  simp only [Function.comp_apply] at hc
  apply (div_le_iff₀ (Real.log_pos hx1)).mpr
  rw [primeContourWidth_log_identity hx1]
  nlinarith only [hc]

end Erdos421
