import ErdosProblems.Erdos421.SmoothedPrimeErrorBound
import ErdosProblems.Erdos421.PrimeContourDecay
import ErdosProblems.Erdos421.PrimeErrorContourAlgebra
import ErdosProblems.Erdos421.PerronPowerBounds

/-! # A decaying majorant for the actual smoothed prime-counting error -/

namespace Erdos421

open Filter Topology

theorem exists_smoothedPrimeError_majorant :
    ∃ D > 0, ∀ᶠ x : ℝ in atTop, ‖smoothedPrimeErrorSum x‖ / x ≤ D *
      (Real.exp (-(primeContourCoefficient / 2) * (Real.log x) ^ (1 / 16 : ℝ)) +
        Real.log x * Real.exp (-(Real.log x) ^ (1 / 16 : ℝ))) := by
  obtain ⟨B, hB, r, hr, H₀, _, C, hC, hbound⟩ := exists_smoothedPrimeError_numeric_bound
  let D : ℝ := 4 * Real.pi * C + 2 * Real.exp 1 * C + 2 * Real.exp 1 * (B + 2)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  filter_upwards [primeContour_fits_eventually hr H₀, primeContour_left_height_decay]
    with x hfit hleft
  obtain ⟨hx, hlog, ha, hab, hb, hbr, hheight, hbδ, hd1⟩ := hfit
  have hxp : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hL : 0 < Real.log x := by linarith
  have hH : 0 < primeContourHeight x := primeContourHeight_pos x
  let E : ℝ := Real.exp (-(primeContourCoefficient / 2) * (Real.log x) ^ (1 / 16 : ℝ))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hraw := hbound x (1 - primeContourWidth x) (1 + 1 / Real.log x) (primeContourHeight x)
    (by linarith) ha hab hb hbr hheight le_rfl hbδ
  have hbinv : 2 / ((1 + 1 / Real.log x) - 1) = 2 * Real.log x := by
    have hLn : Real.log x ≠ 0 := hL.ne'
    field_simp
    ring
  rw [perron_right_power_identity hx1, hbinv] at hraw
  have halgebra := primeError_contour_expression_bound hxp.le hE hlog hH hB.le hC.le
    (Real.rpow_nonneg hxp.le (1 - primeContourWidth x)) hleft (sub_nonneg.mpr hab) hd1
  have hnorm := hraw.trans halgebra
  have htail : Real.log x / primeContourHeight x ≤
      Real.log x * Real.exp (-(Real.log x) ^ (1 / 16 : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left (primeContour_inverse_height_bound hlog) hL.le
    simpa only [mul_one_div] using hm
  have hnorm' : ‖smoothedPrimeErrorSum x‖ ≤ x * D *
      (E + Real.log x * Real.exp (-(Real.log x) ^ (1 / 16 : ℝ))) := by
    apply hnorm.trans
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) (mul_nonneg hxp.le hD.le)
  apply (div_le_iff₀ hxp).mpr
  exact hnorm'.trans_eq (by dsimp only [E]; ring)

end Erdos421
