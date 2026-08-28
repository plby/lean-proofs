import Wikipedia.HopfProblem.SpecialPeriodsModularPullbackLocal
import Wikipedia.HopfProblem.AnalyticPowerGermUniqueness

/-!
# Rotation covariance of the exact local modular pullbacks

The root of unity in a modular power chart is fixed by the actual
Möbius derivative, not chosen as an extra hypothesis.  This gives local
branches satisfying both the prescribed `j` equation and the source's
order-three and order-four rotation laws.
-/

noncomputable section

open Filter Set UpperHalfPlane ModularGroup
open scoped Topology MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

def modularRhoAction (w : ℂ) : ℂ := (w - 1) / w

def modularIAction (w : ℂ) : ℂ := -1 / w

theorem modularRhoAction_coe (z : ℍ) :
    modularRhoAction z = (((T * S) • z : ℍ) : ℂ) := by
  rw [mul_smul, modular_T_smul, modular_S_smul]
  simp only [modularRhoAction, coe_vadd, Complex.ofReal_one, inv_neg]
  field_simp [z.ne_zero]
  ring

theorem modularIAction_coe (z : ℍ) :
    modularIAction z = ((S • z : ℍ) : ℂ) := by
  rw [modular_S_smul]
  simp [modularIAction, inv_neg, div_eq_mul_inv]

theorem modularJ_modularRhoAction {w : ℂ} (hw : w ∈ upperHalfPlaneSet) :
    modularJ (ofComplex (modularRhoAction w)) = modularJ (ofComplex w) := by
  let z : ℍ := ⟨w, hw⟩
  change modularJ (ofComplex (modularRhoAction z)) = modularJ (ofComplex (z : ℂ))
  rw [modularRhoAction_coe, ofComplex_apply, ofComplex_apply]
  exact modularJ_SL_invariant _ _

theorem modularJ_modularIAction {w : ℂ} (hw : w ∈ upperHalfPlaneSet) :
    modularJ (ofComplex (modularIAction w)) = modularJ (ofComplex w) := by
  let z : ℍ := ⟨w, hw⟩
  change modularJ (ofComplex (modularIAction z)) = modularJ (ofComplex (z : ℂ))
  rw [modularIAction_coe, ofComplex_apply, ofComplex_apply]
  exact modularJ_S_invariant _

@[simp] theorem modularRhoAction_rho : modularRhoAction rho = rho := by
  unfold modularRhoAction
  field_simp [rho_ne_zero]
  linear_combination -rho_sq

@[simp] theorem modularIAction_I : modularIAction Complex.I = Complex.I := by
  simp [modularIAction]

theorem modularRhoAction_analyticAt_rho : AnalyticAt ℂ modularRhoAction rho :=
  (analyticAt_id.sub analyticAt_const).div analyticAt_id rho_ne_zero

theorem modularIAction_analyticAt_I : AnalyticAt ℂ modularIAction Complex.I :=
  analyticAt_const.div analyticAt_id Complex.I_ne_zero

theorem modularRhoAction_deriv_rho : deriv modularRhoAction rho = -rho := by
  have h := ((hasDerivAt_id rho).sub_const 1).div (hasDerivAt_id rho) rho_ne_zero
  change HasDerivAt modularRhoAction _ rho at h
  rw [h.deriv]
  simp only [id_eq, one_mul, mul_one]
  field_simp [rho_ne_zero]
  linear_combination rho_cube

theorem modularIAction_deriv_I : deriv modularIAction Complex.I = -1 := by
  have h := (hasDerivAt_const Complex.I (-1 : ℂ)).div
    (hasDerivAt_id Complex.I) Complex.I_ne_zero
  change HasDerivAt modularIAction _ Complex.I at h
  rw [h.deriv]
  norm_num [Complex.I_sq]

theorem modular_cubic_chart_rotation (e : OpenPartialHomeomorph ℂ ℂ)
    (ha : rho ∈ e.source) (he : e rho = 0) (hU : e.source ⊆ upperHalfPlaneSet)
    (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target)
    (hp : ∀ w ∈ e.source, modularJ (ofComplex w) = e w ^ 3) :
    (fun w => e (modularRhoAction w)) =ᶠ[𝓝 rho] (fun w => -rho * e w) := by
  apply analytic_power_chart_equivariant e ha he hf hi
    modularRhoAction_analyticAt_rho modularRhoAction_rho (m := 3) (by decide)
    (by rw [neg_pow, rho_cube]; norm_num) modularRhoAction_deriv_rho
  have hs : ∀ᶠ w in 𝓝 rho, w ∈ e.source := e.open_source.mem_nhds ha
  have hA : ∀ᶠ w in 𝓝 rho, modularRhoAction w ∈ e.source := by
    apply modularRhoAction_analyticAt_rho.continuousAt.preimage_mem_nhds
    simpa only [modularRhoAction_rho] using e.open_source.mem_nhds ha
  filter_upwards [hs, hA] with w hw hAw
  rw [← hp _ hAw, ← hp _ hw]
  exact modularJ_modularRhoAction (hU hw)

theorem modular_quadratic_chart_rotation (e : OpenPartialHomeomorph ℂ ℂ)
    (ha : Complex.I ∈ e.source) (he : e Complex.I = 0)
    (hU : e.source ⊆ upperHalfPlaneSet)
    (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target)
    (hp : ∀ w ∈ e.source, modularJ (ofComplex w) - 1728 = e w ^ 2) :
    (fun w => e (modularIAction w)) =ᶠ[𝓝 Complex.I] (fun w => -1 * e w) := by
  apply analytic_power_chart_equivariant e ha he hf hi
    modularIAction_analyticAt_I modularIAction_I (m := 2) (by decide)
    (by norm_num) modularIAction_deriv_I
  have hs : ∀ᶠ w in 𝓝 Complex.I, w ∈ e.source := e.open_source.mem_nhds ha
  have hA : ∀ᶠ w in 𝓝 Complex.I, modularIAction w ∈ e.source := by
    apply modularIAction_analyticAt_I.continuousAt.preimage_mem_nhds
    simpa only [modularIAction_I] using e.open_source.mem_nhds ha
  filter_upwards [hs, hA] with w hw hAw
  rw [← hp _ hAw, ← hp _ hw, modularJ_modularIAction (hU hw)]

/-- Exact cubic modular pullback with the prescribed elliptic covariance. -/
theorem exists_modularJ_cubic_equivariant_pullback :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (Metric.ball 0 r) ∧ τ 0 = rho ∧
      MapsTo τ (Metric.ball 0 r) upperHalfPlaneSet ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, modularJ (ofComplex (τ s)) = 1728 * s ^ 3) ∧
      analyticOrderAt (fun s => τ s - rho) 0 = 1 ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, τ (-rho * s) = (τ s - 1) / τ s) := by
  obtain ⟨e, ha, he, hU, hf, hi, hp, hpi⟩ := modularJ_rhoPoint_cubic_chart
  obtain ⟨r₀, hr₀, hτ, ht, hs⟩ := exists_disc_inverse_power_branch e ha he hi 12 1 (by decide)
  have hrot := inverse_power_branch_rotation_eventually e ha he hi
    modularRhoAction_analyticAt_rho.continuousAt modularRhoAction_rho
    (k := 1) (by decide) (η := -rho) (by simp) 12
    (modular_cubic_chart_rotation e ha he hU hf hi hp)
  obtain ⟨r₁, hr₁, hrotball⟩ := Metric.mem_nhds_iff.mp hrot
  have hsub : Metric.ball (0 : ℂ) (min r₀ r₁) ⊆ Metric.ball 0 r₀ :=
    Metric.ball_subset_ball (min_le_left _ _)
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, fun s => e.symm (12 * s ^ 1),
    hτ.mono hsub, ?_, fun s hsr => hU (hs s (hsub hsr)), ?_, ?_, ?_⟩
  · simpa only [zero_pow one_ne_zero, mul_zero, he] using e.left_inv ha
  · intro s hsr
    rw [hpi _ (ht s (hsub hsr))]
    ring
  · simpa using analytic_chart_inverse_power_order e ha he hf hi 12 (by norm_num) 1
      (by decide)
  · intro s hsr
    exact hrotball (Metric.ball_subset_ball (min_le_right _ _) hsr)

/-- Exact quartic modular pullback with the prescribed order-four
rotation and quadratic vanishing at the elliptic point. -/
theorem exists_modularJ_quartic_equivariant_pullback :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (Metric.ball 0 r) ∧ τ 0 = Complex.I ∧
      MapsTo τ (Metric.ball 0 r) upperHalfPlaneSet ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r,
        modularJ (ofComplex (τ s)) = 1728 * (1 + s ^ 4)) ∧
      analyticOrderAt (fun s => τ s - Complex.I) 0 = 2 ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, τ (-Complex.I * s) = -1 / τ s) := by
  obtain ⟨e, ha, he, hU, hf, hi, hp, hpi⟩ := modularJ_I_quadratic_chart
  let c : ℂ := 24 * (Real.sqrt 3 : ℂ)
  have hc : c ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)
  have hc2 : c ^ 2 = 1728 := by
    dsimp [c]
    rw [mul_pow, ← Complex.ofReal_pow]
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  obtain ⟨r₀, hr₀, hτ, ht, hs⟩ := exists_disc_inverse_power_branch e ha he hi c 2 (by decide)
  have hrot := inverse_power_branch_rotation_eventually e ha he hi
    modularIAction_analyticAt_I.continuousAt modularIAction_I
    (k := 2) (by decide) (η := -Complex.I) (by norm_num) c
    (modular_quadratic_chart_rotation e ha he hU hf hi hp)
  obtain ⟨r₁, hr₁, hrotball⟩ := Metric.mem_nhds_iff.mp hrot
  have hsub : Metric.ball (0 : ℂ) (min r₀ r₁) ⊆ Metric.ball 0 r₀ :=
    Metric.ball_subset_ball (min_le_left _ _)
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, fun s => e.symm (c * s ^ 2),
    hτ.mono hsub, ?_, fun s hsr => hU (hs s (hsub hsr)), ?_, ?_, ?_⟩
  · simpa only [zero_pow two_ne_zero, mul_zero, he] using e.left_inv ha
  · intro s hsr
    have hh := hpi _ (ht s (hsub hsr))
    rw [mul_pow, hc2] at hh
    linear_combination hh
  · exact analytic_chart_inverse_power_order e ha he hf hi c hc 2 (by decide)
  · intro s hsr
    exact hrotball (Metric.ball_subset_ball (min_le_right _ _) hsr)

end Wikipedia.HopfProblem.SpecialPeriods
