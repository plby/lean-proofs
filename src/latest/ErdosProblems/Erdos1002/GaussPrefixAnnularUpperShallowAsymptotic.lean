import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperShallowCancellation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Asymptotic decay of the upper shallow-cylinder envelope

For fixed `rho > 0`, the shallow cutoff wins half of the retained
midpoint gap after paying for the denominator-good cylinder count.  This
file keeps the resulting exponent calculation explicit and then absorbs
every fixed polynomial tuple count into that exponential margin.
-/

open Filter
open scoped Topology

namespace Erdos1002

noncomputable section

/-- With the chosen denominator tolerance, the uniform shallow exponent
is asymptotic to `-(rho / 2) * log N`. -/
theorem tendsto_upperRetainedShallowUniformExponent_div_log
    {rho : ℝ} (hrho : 0 ≤ rho) :
    Tendsto
      (fun N : ℕ ↦
        upperRetainedShallowUniformExponent rho
            (upperRetainedShallowDenominatorTolerance rho) N /
          Real.log (N : ℝ))
      atTop (nhds (-rho / 2)) := by
  let Delta := upperRetainedShallowDenominatorTolerance rho
  have hH := tendsto_annularDepthAmbientSize_div_log
  have hW := tendsto_annularMidpointBandWidth_div_log hrho
  have hInvLog :
      Tendsto (fun N : ℕ ↦ (Real.log (N : ℝ))⁻¹)
        atTop (nhds 0) := by
    exact
      (tendsto_inv_atTop_zero.comp
        tendsto_log_natCast_atTop).congr'
        (Eventually.of_forall fun _N ↦ rfl)
  have hcalc :=
    ((((hH.mul_const gaussRoofMean).sub
        (hW.mul_const gaussRoofMean)).sub
        (tendsto_const_nhds :
          Tendsto (fun _N : ℕ ↦ (1 : ℝ)) atTop (nhds 1))).add
        (hH.const_mul (3 * Delta))).add
      (hInvLog.const_mul gaussRoofMean)
  have hlimit :
      1 / gaussRoofMean * gaussRoofMean -
            rho / gaussRoofMean * gaussRoofMean -
            1 +
            3 * (gaussRoofMean * rho / 6) *
              (1 / gaussRoofMean) +
            gaussRoofMean * 0 =
          -rho / 2 := by
    field_simp [ne_of_gt gaussRoofMean_pos]
    ring
  have hcalc' :
      Tendsto
        (fun N : ℕ ↦
          ((annularDepthAmbientSize N : ℝ) /
              Real.log (N : ℝ)) * gaussRoofMean -
            ((annularMidpointBandWidth rho N : ℝ) /
              Real.log (N : ℝ)) * gaussRoofMean -
            1 +
            (3 * Delta) *
              ((annularDepthAmbientSize N : ℝ) /
                Real.log (N : ℝ)) +
            gaussRoofMean * (Real.log (N : ℝ))⁻¹)
        atTop (nhds (-rho / 2)) := by
    rw [← hlimit]
    simpa only [Delta, upperRetainedShallowDenominatorTolerance] using!
      hcalc
  apply hcalc'.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  unfold upperRetainedShallowUniformExponent
  field_simp [ne_of_gt hlog]
  ring

/-- For positive `rho`, the upper shallow exponent is eventually bounded
by the strict negative margin `-(rho / 4) * log N`. -/
theorem eventually_upperRetainedShallowUniformExponent_le_neg_log
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ N : ℕ in atTop,
      upperRetainedShallowUniformExponent rho
          (upperRetainedShallowDenominatorTolerance rho) N ≤
        -(rho / 4) * Real.log (N : ℝ) := by
  have hlimit : -rho / 2 < -(rho / 4) := by linarith
  have hratio :=
    (tendsto_upperRetainedShallowUniformExponent_div_log
      hrho.le).eventually_lt_const hlimit
  filter_upwards
    [hratio, tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
      N hratioN hlog
  have hmul :=
    mul_le_mul_of_nonneg_right hratioN.le hlog.le
  have hrewrite :
      upperRetainedShallowUniformExponent rho
            (upperRetainedShallowDenominatorTolerance rho) N =
          (upperRetainedShallowUniformExponent rho
              (upperRetainedShallowDenominatorTolerance rho) N /
            Real.log (N : ℝ)) *
            Real.log (N : ℝ) := by
    field_simp [ne_of_gt hlog]
  rw [hrewrite]
  exact hmul

private theorem upperShallow_eventually_const_mul_pow_le_exp
    (C : ℝ) (r : ℕ) (b : ℝ) (hC : 0 ≤ C) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, C * x ^ r ≤ Real.exp (b * x) := by
  have hlittle :=
    (isLittleO_pow_exp_pos_mul_atTop r hb).const_mul_left C
  have hbound := hlittle.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hleft : 0 ≤ C * x ^ r :=
    mul_nonneg hC (pow_nonneg hx0 r)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hleft,
    abs_of_pos (Real.exp_pos _), one_mul] using! hx

/-- Every fixed nonnegative polynomial in the annular depth horizon is
absorbed by the upper shallow-cylinder exponential margin. -/
theorem
    tendsto_const_mul_annularDepth_pow_mul_exp_upperShallowUniform_zero
    (C : ℝ) (r : ℕ) (hC : 0 ≤ C)
    {rho : ℝ} (hrho : 0 < rho) :
    Tendsto
      (fun N : ℕ ↦
        C * (annularDepthAmbientSize N : ℝ) ^ r *
          Real.exp
            (upperRetainedShallowUniformExponent rho
              (upperRetainedShallowDenominatorTolerance rho) N))
      atTop (nhds 0) := by
  let c : ℝ := rho / 4
  let b : ℝ := c / 2
  let D : ℝ := 1 / gaussRoofMean + 1
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos hrho (by norm_num)
  have hb : 0 < b := half_pos hc
  have hD : 0 < D := by
    dsimp only [D]
    exact add_pos (one_div_pos.mpr gaussRoofMean_pos) zero_lt_one
  have hratio :
      ∀ᶠ N : ℕ in atTop,
        (annularDepthAmbientSize N : ℝ) /
            Real.log (N : ℝ) < D := by
    apply tendsto_annularDepthAmbientSize_div_log.eventually_lt_const
    dsimp only [D]
    linarith
  have hdepth :
      ∀ᶠ N : ℕ in atTop,
        (annularDepthAmbientSize N : ℝ) ≤
          D * Real.log (N : ℝ) := by
    filter_upwards
      [hratio,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
        N hratioN hlog
    have hmul :=
      mul_le_mul_of_nonneg_right hratioN.le hlog.le
    calc
      (annularDepthAmbientSize N : ℝ) =
          ((annularDepthAmbientSize N : ℝ) /
            Real.log (N : ℝ)) * Real.log (N : ℝ) := by
              field_simp [ne_of_gt hlog]
      _ ≤ D * Real.log (N : ℝ) := hmul
  have hpolyReal :
      ∀ᶠ x : ℝ in atTop,
        (C * D ^ r) * x ^ r ≤ Real.exp (b * x) :=
    upperShallow_eventually_const_mul_pow_le_exp
      (C * D ^ r) r b
      (mul_nonneg hC (pow_nonneg hD.le r)) hb
  have hpoly :
      ∀ᶠ N : ℕ in atTop,
        (C * D ^ r) * Real.log (N : ℝ) ^ r ≤
          Real.exp (b * Real.log (N : ℝ)) :=
    tendsto_log_natCast_atTop.eventually hpolyReal
  have hexponent :=
    eventually_upperRetainedShallowUniformExponent_le_neg_log hrho
  have hupper :
      ∀ᶠ N : ℕ in atTop,
        C * (annularDepthAmbientSize N : ℝ) ^ r *
            Real.exp
              (upperRetainedShallowUniformExponent rho
                (upperRetainedShallowDenominatorTolerance rho) N) ≤
          Real.exp (-b * Real.log (N : ℝ)) := by
    filter_upwards
      [hdepth, hpoly, hexponent,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
        N hdepthN hpolyN hexponentN hlog
    have hdepthPow :
        (annularDepthAmbientSize N : ℝ) ^ r ≤
          (D * Real.log (N : ℝ)) ^ r :=
      pow_le_pow_left₀ (by positivity) hdepthN r
    have hcount :
        C * (annularDepthAmbientSize N : ℝ) ^ r ≤
          (C * D ^ r) * Real.log (N : ℝ) ^ r := by
      calc
        C * (annularDepthAmbientSize N : ℝ) ^ r ≤
            C * (D * Real.log (N : ℝ)) ^ r :=
          mul_le_mul_of_nonneg_left hdepthPow hC
        _ = (C * D ^ r) * Real.log (N : ℝ) ^ r := by
          rw [mul_pow]
          ring
    have hexp :
        Real.exp
            (upperRetainedShallowUniformExponent rho
              (upperRetainedShallowDenominatorTolerance rho) N) ≤
          Real.exp (-c * Real.log (N : ℝ)) :=
      Real.exp_le_exp.mpr (by simpa only [c] using! hexponentN)
    calc
      C * (annularDepthAmbientSize N : ℝ) ^ r *
          Real.exp
            (upperRetainedShallowUniformExponent rho
              (upperRetainedShallowDenominatorTolerance rho) N) ≤
          ((C * D ^ r) * Real.log (N : ℝ) ^ r) *
            Real.exp (-c * Real.log (N : ℝ)) :=
        mul_le_mul hcount hexp (Real.exp_pos _).le
          (mul_nonneg
            (mul_nonneg hC (pow_nonneg hD.le r))
            (pow_nonneg hlog.le r))
      _ ≤
          Real.exp (b * Real.log (N : ℝ)) *
            Real.exp (-c * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hpolyN (Real.exp_pos _).le
      _ = Real.exp (-b * Real.log (N : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [b]
        ring
  have hlinear :
      Tendsto (fun N : ℕ ↦ b * Real.log (N : ℝ)) atTop atTop :=
    tendsto_log_natCast_atTop.const_mul_atTop hb
  have hdecay :
      Tendsto
        (fun N : ℕ ↦ Real.exp (-b * Real.log (N : ℝ)))
        atTop (nhds 0) := by
    have h :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear
    convert! h using 1
    funext N
    dsimp only [Function.comp_apply]
    congr 1
    ring
  exact squeeze_zero'
    (Eventually.of_forall fun N ↦ by positivity) hupper hdecay

end

end Erdos1002
