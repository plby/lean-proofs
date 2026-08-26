import ErdosProblems.Erdos421.PrimeContourParameters

/-! # Admissibility and decay of the explicit prime-counting contour -/

namespace Erdos421

open Filter Topology

theorem primeContour_fits_eventually {r : ℝ} (hr : 0 < r) (H₀ : ℝ) :
    ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧ 1 ≤ Real.log x ∧
      1 / 2 ≤ 1 - primeContourWidth x ∧
      1 - primeContourWidth x ≤ 1 + 1 / Real.log x ∧
      1 < 1 + 1 / Real.log x ∧ 1 + 1 / Real.log x < 1 + r ∧
      H₀ ≤ primeContourHeight x ∧ 1 + 1 / Real.log x ≤ 1 + primeContourWidth x ∧
      (1 + 1 / Real.log x) - (1 - primeContourWidth x) ≤ 1 := by
  have hinv := Real.tendsto_log_atTop.const_div_atTop (1 : ℝ)
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    primeContourWidth_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hinv.eventually (gt_mem_nhds hr),
    primeContourHeight_tendsto.eventually (eventually_ge_atTop H₀),
    primeContourWidth_dominates_right_gap] with x hx hlog hwidth hinv hheight hcover
  have hw : 0 < primeContourWidth x := primeContourWidth_pos (by linarith)
  have hi : 0 < 1 / Real.log x := by positivity
  exact ⟨hx, hlog, by linarith, by linarith, by linarith, by linarith, hheight,
    by linarith, by linarith⟩

theorem primeContour_left_height_decay :
    ∀ᶠ x : ℝ in atTop, x ^ (1 - primeContourWidth x) * primeContourHeight x ≤
      x * Real.exp (-(primeContourCoefficient / 2) * (Real.log x) ^ (1 / 16 : ℝ)) := by
  have hc : 0 < primeContourCoefficient / 2 := by have := primeContourCoefficient_pos; positivity
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 33 / 64)).comp
    Real.tendsto_log_atTop
  filter_upwards [ht.eventually (gt_mem_nhds hc), eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with x hsave hx hlog
  have hx1 : 1 < x := by linarith
  have hxp : 0 < x := by linarith
  have hL : 0 < Real.log x := by linarith
  have hratio : (Real.log x) ^ (1 / 4 : ℝ) / (Real.log x) ^ (49 / 64 : ℝ) ≤
      primeContourCoefficient / 2 := by
    rw [← Real.rpow_sub hL, show (1 / 4 : ℝ) - 49 / 64 = -(33 / 64) by norm_num]
    exact hsave.le
  have hbudget := (div_le_iff₀ (Real.rpow_pos_of_pos hL (49 / 64 : ℝ))).mp hratio
  have hpow : (Real.log x) ^ (1 / 16 : ℝ) ≤ (Real.log x) ^ (49 / 64 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hpow hc.le
  calc
    _ = Real.exp (Real.log x * (1 - primeContourWidth x) + (Real.log x) ^ (1 / 4 : ℝ)) := by
      rw [Real.rpow_def_of_pos hxp, primeContourHeight, ← Real.exp_add]
    _ = Real.exp (Real.log x + ((Real.log x) ^ (1 / 4 : ℝ) -
        primeContourWidth x * Real.log x)) := by congr 1; ring
    _ = x * Real.exp ((Real.log x) ^ (1 / 4 : ℝ) -
        primeContourCoefficient * (Real.log x) ^ (49 / 64 : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hxp, primeContourWidth_log_identity hx1]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith only [hbudget, hscaled])) hxp.le

theorem primeContour_inverse_height_bound {x : ℝ} (hlog : 1 ≤ Real.log x) :
    1 / primeContourHeight x ≤ Real.exp (-(Real.log x) ^ (1 / 16 : ℝ)) := by
  rw [primeContourHeight, one_div, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1 / 16 : ℝ) ≤ 1 / 4))

end Erdos421
