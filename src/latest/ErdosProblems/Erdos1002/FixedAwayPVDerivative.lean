import ErdosProblems.Erdos1002.FixedAwaySmoothCutoff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Differentiating the fixed-away principal-value transform

The singular principal part is locally constant away from frequency zero.
Differentiating the compact paired correction under its finite interval
integral therefore gives the exact cosine-transform formula for `Rχ'` on
both open half-lines.  The exceptional integration point `v = 0` is removed
only as a null set; no illicit pointwise division at zero is used.
-/

open Filter MeasureTheory Set
open scoped ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

private theorem sineKernel_parameter_eq (v y : ℝ) (hv : v ≠ 0) :
    sineKernel (2 * Real.pi * y) v =
      Real.sin ((2 * Real.pi * y) * v) / v := by
  by_cases hy : y = 0
  · subst y
    simp [sineKernel]
  · unfold sineKernel
    rw [Real.sinc_of_ne_zero]
    · field_simp
    · exact mul_ne_zero (mul_ne_zero (by positivity) hy) hv

private theorem hasDerivAt_cutoff_sineKernel_parameter
    (κ : ℝ → ℝ) (v y : ℝ) (hv : v ≠ 0) :
    HasDerivAt
      (fun z : ℝ ↦ κ v * sineKernel (2 * Real.pi * z) v)
      (2 * Real.pi * κ v * Real.cos ((2 * Real.pi * y) * v)) y := by
  have hfun : (fun z : ℝ ↦ κ v * sineKernel (2 * Real.pi * z) v) =
      fun z : ℝ ↦ κ v * (Real.sin ((2 * Real.pi * z) * v) / v) := by
    funext z
    rw [sineKernel_parameter_eq v z hv]
  rw [hfun]
  have harg : HasDerivAt (fun z : ℝ ↦ (2 * Real.pi * z) * v)
      ((2 * Real.pi) * v) y := by
    simpa only [id_eq, mul_one] using!
      (((hasDerivAt_id y).const_mul (2 * Real.pi)).mul_const v)
  have hraw := (harg.sin.div_const v).const_mul (κ v)
  convert! hraw using 1
  field_simp

theorem hasDerivAt_compactCutoffPairedSine
    (κ : ℝ → ℝ) (C y : ℝ) (hκcont : Continuous κ) :
    HasDerivAt (compactCutoffPairedSine κ C)
      (∫ v in (0 : ℝ)..C,
        2 * Real.pi * κ v * Real.cos ((2 * Real.pi * y) * v)) y := by
  let F : ℝ → ℝ → ℝ := fun z v ↦
    κ v * sineKernel (2 * Real.pi * z) v
  let F' : ℝ → ℝ → ℝ := fun z v ↦
    2 * Real.pi * κ v * Real.cos ((2 * Real.pi * z) * v)
  let bound : ℝ → ℝ := fun v ↦ 2 * Real.pi * |κ v|
  have hFcont (z : ℝ) : Continuous (F z) := by
    dsimp [F]
    unfold sineKernel
    fun_prop
  have hF'cont (z : ℝ) : Continuous (F' z) := by
    dsimp [F']
    fun_prop
  have hboundcont : Continuous bound := by
    dsimp [bound]
    fun_prop
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (x₀ := y)
    (a := (0 : ℝ)) (b := C) (s := Set.univ)
    (show Set.univ ∈ nhds y from univ_mem)
    (by
      filter_upwards with z
      exact (hFcont z).aestronglyMeasurable)
    ((hFcont y).intervalIntegrable 0 C)
    ((hF'cont y).aestronglyMeasurable)
    (by
      filter_upwards with v hv
      intro z hz
      dsimp [F', bound]
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        2 * Real.pi * |κ v| * |Real.cos ((2 * Real.pi * z) * v)| ≤
            2 * Real.pi * |κ v| * 1 := by
          gcongr
          exact Real.abs_cos_le_one _
        _ = 2 * Real.pi * |κ v| := by ring)
    (hboundcont.intervalIntegrable 0 C)
    (by
      filter_upwards [(volume : Measure ℝ).ae_ne 0] with v hv hvmem
      intro z hz
      exact hasDerivAt_cutoff_sineKernel_parameter κ v z hv)
  simpa only [compactCutoffPairedSine, F, F'] using! h.2

theorem hasDerivAt_compactCutoffPVCorrection
    (κ : ℝ → ℝ) (C y : ℝ) (hκcont : Continuous κ) :
    HasDerivAt (compactCutoffPVCorrection κ C)
      ((-2 * Complex.I) *
        ((∫ v in (0 : ℝ)..C,
          2 * Real.pi * κ v * Real.cos ((2 * Real.pi * y) * v) : ℝ) : ℂ)) y := by
  have hreal := hasDerivAt_compactCutoffPairedSine κ C y hκcont
  have hcast := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y hreal
  have hmul := hcast.const_mul (-2 * Complex.I)
  simpa only [compactCutoffPVCorrection, Function.comp_apply,
    Complex.ofRealCLM_apply] using! hmul

theorem hasDerivAt_signedExponentialPV_of_ne
    {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt signedExponentialPV 0 y := by
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · have heq : signedExponentialPV =ᶠ[nhds y]
        fun _z : ℝ ↦ Complex.I * Real.pi := by
      filter_upwards [gt_mem_nhds hyneg] with z hz
      simp [signedExponentialPV, hz, not_lt.mpr hz.le]
    exact (hasDerivAt_const y (Complex.I * Real.pi)).congr_of_eventuallyEq
      heq
  · have heq : signedExponentialPV =ᶠ[nhds y]
        fun _z : ℝ ↦ -Complex.I * Real.pi := by
      filter_upwards [lt_mem_nhds hypos] with z hz
      simp [signedExponentialPV, hz]
    exact (hasDerivAt_const y (-Complex.I * Real.pi)).congr_of_eventuallyEq
      heq

theorem hasDerivAt_fixedAwayPVTransform_of_ne
    (κ : ℝ → ℝ) (C : ℝ) {y : ℝ} (hκcont : Continuous κ)
    (hy : y ≠ 0) :
    HasDerivAt (fixedAwayPVTransform κ C)
      ((2 * Complex.I) *
        ((∫ v in (0 : ℝ)..C,
          2 * Real.pi * κ v * Real.cos ((2 * Real.pi * y) * v) : ℝ) : ℂ)) y := by
  have hsigned := hasDerivAt_signedExponentialPV_of_ne hy
  have hcorr := hasDerivAt_compactCutoffPVCorrection κ C y hκcont
  change HasDerivAt
    (signedExponentialPV - compactCutoffPVCorrection κ C) _ y
  convert! hsigned.sub hcorr using 1
  ring

end

end Erdos1002
