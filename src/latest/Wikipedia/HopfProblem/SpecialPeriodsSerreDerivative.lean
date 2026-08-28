import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
# The Serre derivative as an actual modular form

The normalized derivative of a holomorphic modular form tends to zero at
the cusp: in the local parameter `q`, it is `q` times the derivative of the
analytic cusp function.  Together with the convergent Fourier expansion
of `E₂`, this supplies the cusp bound missing from the slash-equivariance
calculation and constructs the weight-raising Serre derivative.
-/

noncomputable section

open Function Filter Set UpperHalfPlane
open scoped Topology Manifold MatrixGroups ModularForm

namespace Wikipedia.HopfProblem.SpecialPeriods

private theorem hasDerivAt_qParam_one (z : ℂ) :
    HasDerivAt (Periodic.qParam 1)
      ((2 * Real.pi * Complex.I) * Periodic.qParam 1 z) z := by
  change HasDerivAt (fun w : ℂ => Complex.exp ((2 * Real.pi * Complex.I) * w / 1))
    ((2 * Real.pi * Complex.I) * Complex.exp ((2 * Real.pi * Complex.I) * z / 1)) z
  simpa [Periodic.qParam, mul_comm] using
    ((hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp

/-- The exact derivative in the analytic cusp coordinate, at every point
of the upper half-plane. -/
theorem normalizedDerivOfComplex_eq_q_mul_deriv {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (z : ℍ) :
    Derivative.normalizedDerivOfComplex f z =
      Periodic.qParam 1 z * deriv (cuspFunction 1 f) (Periodic.qParam 1 z) := by
  have hdiff := ModularFormClass.differentiableAt_cuspFunction f
    zero_lt_one one_mem_strictPeriods_SL
    (Periodic.norm_qParam_lt_one zero_lt_one z.im_pos)
  have hcomp := hdiff.hasDerivAt.comp (z : ℂ) (hasDerivAt_qParam_one z)
  have heq : (f ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)]
      (fun w => cuspFunction 1 f (Periodic.qParam 1 w)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    have h := SlashInvariantFormClass.eq_cuspFunction f (⟨w, hw⟩ : ℍ)
      one_mem_strictPeriods_SL one_ne_zero
    simpa [Function.comp_apply, ofComplex_apply_of_im_pos hw] using h.symm
  have hd := (hcomp.congr_of_eventuallyEq heq).deriv
  rw [Derivative.normalizedDerivOfComplex, hd]
  field_simp [Complex.two_pi_I_ne_zero]

/-- No bounded-derivative assumption is needed: analyticity at the cusp
gives the vanishing limit of the normalized derivative. -/
theorem normalizedDerivOfComplex_tendsto_zero {k : ℤ}
    (f : ModularForm 𝒮ℒ k) :
    Tendsto (Derivative.normalizedDerivOfComplex f) atImInfty (𝓝 0) := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f
    zero_lt_one one_mem_strictPeriods_SL
  have ht := (qParam_tendsto_atImInfty (h := 1) zero_lt_one).mul
    (ha.deriv.continuousAt.tendsto.comp (qParam_tendsto_atImInfty zero_lt_one))
  simpa only [zero_mul, Function.comp_def,
    ← normalizedDerivOfComplex_eq_q_mul_deriv] using ht

/-- The correction term `E₂` has strict period one, despite not being a
modular form of weight two. -/
theorem E2_periodic_comp_ofComplex :
    Periodic (EisensteinSeries.E2 ∘ ofComplex) (1 : ℂ) := by
  have hT (z : ℍ) : EisensteinSeries.E2 ((1 : ℝ) +ᵥ z) = EisensteinSeries.E2 z := by
    have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.T) z
    rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul] at h
    have hd : denom (ModularGroup.T : SL(2, ℤ)) z = 1 := by
      rw [ModularGroup.denom_apply]
      rw [ModularGroup.coe_T]
      norm_num
    simpa only [hd, one_zpow, mul_one, EisensteinSeries.D2_T,
      smul_zero, sub_zero] using h
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + 1).im := by simpa using hw
    have hz : ofComplex (w + 1) = (1 : ℝ) +ᵥ (⟨w, hw⟩ : ℍ) := by
      apply UpperHalfPlane.ext
      simp [ofComplex_apply_of_im_pos hw', add_comm]
    simpa [Function.comp_apply, hz, ofComplex_apply_of_im_pos hw] using hT ⟨w, hw⟩
  · have hw' : (w + 1).im ≤ 0 := by simpa using le_of_not_gt hw
    simp [Function.comp_apply, ofComplex_apply_of_im_nonpos hw',
      ofComplex_apply_of_im_nonpos (le_of_not_gt hw)]

theorem E2_cuspFunction_analyticAt_zero :
    AnalyticAt ℂ (cuspFunction 1 EisensteinSeries.E2) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one E2_periodic_comp_ofComplex
    E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2

/-- The Fourier expansion, using the same parameter as the cusp function. -/
theorem E2_hasSum_qParam (z : ℍ) : HasSum (fun m : ℕ =>
      (if m = 0 then (1 : ℂ) else -24 * (ArithmeticFunction.sigma 1 m : ℂ)) •
        Periodic.qParam 1 z ^ m) (EisensteinSeries.E2 z) := by
  simpa only [Periodic.qParam, Complex.ofReal_one, div_one] using
    EisensteinSeries.hasSum_qExpansion_E2 (z := z)

private theorem cuspFunction_zero_of_hasSum (f : ℍ → ℂ) (c : ℕ → ℂ)
    (ha : AnalyticAt ℂ (cuspFunction 1 f) 0)
    (hs : ∀ z : ℍ, HasSum (fun m => c m • Periodic.qParam 1 z ^ m) (f z)) :
    cuspFunction 1 f 0 = c 0 := by
  have h := (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction
    (h := 1) (f := f) (c := c) zero_lt_one ha hs).coeff_zero (fun i => Fin.elim0 i)
  simpa using h.symm

/-- The constant term is obtained from the actual convergent Eisenstein
series, not postulated as a normalization condition. -/
theorem E2_cuspFunction_zero : cuspFunction 1 EisensteinSeries.E2 0 = 1 := by
  exact cuspFunction_zero_of_hasSum EisensteinSeries.E2
    (fun m => if m = 0 then (1 : ℂ) else -24 * (ArithmeticFunction.sigma 1 m : ℂ))
    E2_cuspFunction_analyticAt_zero E2_hasSum_qParam

theorem E2_qExpansion_coeff_zero :
    (qExpansion 1 EisensteinSeries.E2).coeff 0 = 1 := by
  have h := E2_cuspFunction_zero
  simpa only [qExpansion_coeff, Nat.factorial_zero, Nat.cast_one, inv_one,
    iteratedDeriv_zero, one_mul] using h

theorem E2_tendsto_one : Tendsto EisensteinSeries.E2 atImInfty (𝓝 1) := by
  have h := E2_cuspFunction_analyticAt_zero.continuousAt.tendsto.comp
    (qParam_tendsto_atImInfty (h := 1) zero_lt_one)
  simpa only [Function.comp_def, E2_cuspFunction_zero,
    UpperHalfPlane.eq_cuspFunction _ one_ne_zero E2_periodic_comp_ofComplex] using h

theorem modularForm_tendsto_qExpansion_coeff_zero {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Tendsto f atImInfty (𝓝 ((qExpansion 1 f).coeff 0)) := by
  have h := (ModularFormClass.analyticAt_cuspFunction_zero f
    zero_lt_one one_mem_strictPeriods_SL).continuousAt.tendsto.comp
    (qParam_tendsto_atImInfty (h := 1) zero_lt_one)
  simpa [Function.comp_def, qExpansion_coeff,
    SlashInvariantFormClass.eq_cuspFunction f _ one_mem_strictPeriods_SL one_ne_zero] using h

theorem serreDerivative_tendsto {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Tendsto (Derivative.serreDerivative k f) atImInfty
      (𝓝 (-(k : ℂ) / 12 * (qExpansion 1 f).coeff 0)) := by
  have h := (normalizedDerivOfComplex_tendsto_zero f).sub
    (((tendsto_const_nhds (x := (k : ℂ) * 12⁻¹)).mul E2_tendsto_one).mul
      (modularForm_tendsto_qExpansion_coeff_zero f))
  convert h using 1
  · ext z
    rfl
  · congr 1
    ring

theorem serreDerivative_boundedAtImInfty {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    IsBoundedAtImInfty (Derivative.serreDerivative k f) :=
  (serreDerivative_tendsto f).isBigO_one ℝ

/-- The actual weight-raising Serre derivative on level-one modular forms.
Holomorphicity, all slash identities, and boundedness at every cusp are
proved from the supplied modular form. -/
def serreDerivativeModularForm {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ModularForm 𝒮ℒ (k + 2) where
  toFun := Derivative.serreDerivative k f
  slash_action_eq' γ hγ := by
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
    apply Derivative.serreDerivative_slash_invariant (ModularFormClass.holo f)
    exact SlashInvariantFormClass.slash_action_eq f g (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
  holo' := Derivative.serreDerivative_mdifferentiable k (ModularFormClass.holo f)
  bdd_at_cusps' hc := by
    apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
    intro γ hγ
    rw [Derivative.serreDerivative_slash_invariant (ModularFormClass.holo f)
      (SlashInvariantFormClass.slash_action_eq f γ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩))]
    exact serreDerivative_boundedAtImInfty f

@[simp] theorem serreDerivativeModularForm_apply {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (z : ℍ) :
    serreDerivativeModularForm f z = Derivative.serreDerivative k f z := rfl

@[simp] theorem coe_serreDerivativeModularForm {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ⇑(serreDerivativeModularForm f) = Derivative.serreDerivative k f := rfl

/-- The exact constant Fourier coefficient of the constructed Serre
derivative. -/
theorem serreDerivativeModularForm_qExpansion_coeff_zero {k : ℤ}
    (f : ModularForm 𝒮ℒ k) :
    (qExpansion 1 (serreDerivativeModularForm f)).coeff 0 =
      -(k : ℂ) / 12 * (qExpansion 1 f).coeff 0 := by
  apply tendsto_nhds_unique (modularForm_tendsto_qExpansion_coeff_zero
    (serreDerivativeModularForm f))
  exact serreDerivative_tendsto f

end Wikipedia.HopfProblem.SpecialPeriods
