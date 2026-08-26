import ErdosProblems.Erdos788.ChosenParameterBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Eventual regularity of the chosen parameters

This file discharges the elementary asymptotic hypotheses isolated in
`ParameterRegular`.  Keeping this argument separate means that all finite
construction modules remain pointwise and threshold-free.
-/

namespace Erdos788

private theorem log_nat_tendsto_atTop :
    Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ))
      Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop)

private theorem loglog_nat_tendsto_atTop :
    Filter.Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)))
      Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp log_nat_tendsto_atTop

/-- The explicit exponent correction tends to zero. -/
theorem exponentCorrection_tendsto_zero :
    Filter.Tendsto exponentCorrection Filter.atTop (nhds 0) := by
  have hratioReal :
      Filter.Tendsto (fun x : ℝ => Real.log x / x)
        Filter.atTop (nhds 0) := by
    simpa [Function.id_def] using!
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hratioNat := hratioReal.comp log_nat_tendsto_atTop
  have hrpow := hratioNat.rpow_const
    (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3))
  change Filter.Tendsto
    (fun N : ℕ =>
      (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) ^ (1 / 3 : ℝ))
    Filter.atTop (nhds 0)
  simpa only [Function.comp_apply, one_div,
    Real.zero_rpow (by norm_num : (3 : ℝ)⁻¹ ≠ 0)] using! hrpow

/-- The correction still tends to zero after multiplication by `log log N`. -/
theorem correction_mul_loglog_tendsto_zero :
    Filter.Tendsto
      (fun N : ℕ => exponentCorrection N *
        Real.log (Real.log (N : ℝ)))
      Filter.atTop (nhds 0) := by
  have hpowerReal :
      Filter.Tendsto
        (fun x : ℝ => Real.log x ^ (4 / 3 : ℝ) / x ^ (1 / 3 : ℝ))
        Filter.atTop (nhds 0) := by
    simpa using!
      (isLittleO_log_rpow_rpow_atTop (4 / 3 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 3)).tendsto_div_nhds_zero
  have hpowerNat := hpowerReal.comp log_nat_tendsto_atTop
  have heq :
      (fun N : ℕ => exponentCorrection N *
          Real.log (Real.log (N : ℝ))) =ᶠ[Filter.atTop]
        (fun N : ℕ =>
          Real.log (Real.log (N : ℝ)) ^ (4 / 3 : ℝ) /
            Real.log (N : ℝ) ^ (1 / 3 : ℝ)) := by
    filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0,
      loglog_nat_tendsto_atTop.eventually_gt_atTop 0] with N hL hq
    rw [exponentCorrection, Real.div_rpow hq.le hL.le]
    rw [div_mul_eq_mul_div, ← Real.rpow_add_one hq.ne']
    norm_num
  exact hpowerNat.congr' heq.symm

/-- The bundled pointwise hypotheses used by the parameter calculation hold
for every sufficiently large integer. -/
theorem eventually_parameterRegular :
    ∀ᶠ N : ℕ in Filter.atTop, ParameterRegular N := by
  have hproduct :
      Filter.Tendsto
        (fun N : ℕ => exponentCorrection N *
          (Real.log (Real.log (N : ℝ)) + Real.log 4))
        Filter.atTop (nhds 0) := by
    have hconst := exponentCorrection_tendsto_zero.mul_const (Real.log 4)
    have hadd := correction_mul_loglog_tendsto_zero.add hconst
    simpa [mul_add] using! hadd
  have hscaled :
      Filter.Tendsto
        (fun N : ℕ => 400000000 * exponentCorrection N)
        Filter.atTop (nhds 0) := by
    simpa [mul_comm] using!
      exponentCorrection_tendsto_zero.mul_const (400000000 : ℝ)
  filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0,
    loglog_nat_tendsto_atTop.eventually_ge_atTop 2,
    (tendsto_order.1 hproduct).2 1 (by norm_num),
    (tendsto_order.1 hscaled).2 1 (by norm_num)] with N hL hq hproductN hscaledN
  exact ⟨hL, hq, hproductN.le, hscaledN.le⟩

/-- A concrete natural threshold exists for `ParameterRegular`. -/
theorem exists_parameterRegular_threshold :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ParameterRegular N := by
  simpa only [Filter.eventually_atTop] using! eventually_parameterRegular

end Erdos788
