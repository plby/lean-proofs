import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauMarking
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauCuspMonodromy
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauNormalizationTranslations
import Wikipedia.HopfProblem.SpecialPeriodsTauCusp

/-!
# A normalized covariant global lift from the actual triangle source data

The global modular-germ lifting theorem, the constructed simple-pole cusp
branch, and the integral simultaneous-normalization theorem now combine
to construct the special `τ` from a supplied invariant source function.
No global lift, marked value, covariance law, or cusp monodromy is an
input to this construction.  The normalizing modular change is proved
to be an integer translation, so the analytic cusp expansion is retained.

The hypotheses describe the source function required in §3.1.  This file
does not assert that the actual triangle quotient has already been
uniformized or that its marked global coordinate has been constructed.
-/

noncomputable section

open Filter Set UpperHalfPlane ModularGroup Matrix
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The actual global modular lift, simultaneous elliptic normalization,
generator equations and analytic cusp expansion all follow from the
invariant source function, its branch orders and its meromorphic simple
pole.  None of these properties of the lift is an extra assumption. -/
theorem exists_covariant_tau_of_triangle_source (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (h₃ : ∀ a : ℍ, F a = 0 →
      ∃ k : ℕ, analyticOrderAt (F ∘ ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ : ∀ a : ℍ, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F (ofComplex z) - 1728)
        (a : ℂ) = (2 * k : ℕ))
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = F z)
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z)
    (horder₁ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerOne : ℂ) = 3)
    (horder₂ : analyticOrderAt (fun z : ℂ => F (ofComplex z) - 1728)
      (Triangle.centerTwo : ℂ) = 4)
    (Fc : ℂ → ℂ) (hFc : MeromorphicAt Fc 0)
    (hFcorder : meromorphicOrderAt Fc 0 = (-1 : ℤ))
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hsource : ∀ z : ℍ, ‖Function.Periodic.qParam Triangle.width (z : ℂ)‖ < r₀ →
      F z = Fc (Function.Periodic.qParam Triangle.width (z : ℂ))) :
    ∃ τ : ℍ → ℍ, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ ∧
      (∀ z : ℍ, modularJ (τ z) = F z) ∧ TauCovariant τ ∧
      τ Triangle.centerOne = rhoPoint ∧ τ Triangle.centerTwo = UpperHalfPlane.I ∧
      ∃ r > 0, r < r₀ ∧ r < 1 ∧ ∃ h : ℂ → ℂ,
        AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
        ∀ z : ℍ, ‖Function.Periodic.qParam Triangle.width (z : ℂ)‖ < r →
          (τ z : ℂ) = TauCusp.correctedLogarithmWidth Triangle.width h (z : ℂ) := by
  have hFa : F Triangle.centerOne = 0 := by
    have hh := (analyticOrderAt_ne_zero.mp (show
      analyticOrderAt (F ∘ ofComplex) (Triangle.centerOne : ℂ) ≠ 0 by
        rw [horder₁]; norm_num)).2
    simpa only [Function.comp_apply, ofComplex_apply] using hh
  have hFb : F Triangle.centerTwo = 1728 := by
    have hh := (analyticOrderAt_ne_zero.mp (show
      analyticOrderAt (fun z : ℂ => F (ofComplex z) - 1728)
        (Triangle.centerTwo : ℂ) ≠ 0 by rw [horder₂]; norm_num)).2
    exact sub_eq_zero.mp (by simpa only [ofComplex_apply] using hh)
  obtain ⟨_, _, _, τ, hτ, hJ, r, hr, hrr₀, hr1, h, hh, _, hformula⟩ :=
    TauCusp.exists_global_normalized_lift_of_simplePole_cusp F hF h₃ h₂
      Triangle.width Triangle.width_pos Fc hFc hFcorder hr₀ hsource
  have hC := tau_cusp_monodromy_of_formula hτ hr hformula
  have hCtr : Matrix.trace (T⁻¹).val = 2 ∨ Matrix.trace (T⁻¹).val = -2 := by
    left
    rw [modularSL_trace_inv]
    norm_num [Matrix.trace_fin_two, T]
  obtain ⟨γ, hcov, hγa, hγb⟩ := exists_normalized_covariant_modular_translate F hτ hJ
    hFa hFb hF₁ hF₂ horder₁ horder₂ T⁻¹ hCtr hC
  have hab : τ Triangle.centerOne ≠ τ Triangle.centerTwo := by
    intro he
    have hj := congrArg modularJ he
    rw [hJ, hJ, hFa, hFb] at hj
    norm_num at hj
  have hcomm := modular_translate_commutes_Tinv_of_cusp_covariance γ hC hcov
    Triangle.centerOne Triangle.centerTwo hab
  obtain ⟨n, hn⟩ := modularSL_integer_translation_coe_of_commutes_T_inv_action γ hcomm
  refine ⟨fun z => γ • τ z, (modularSL_holomorphic γ).comp hτ,
    (fun z => (modularJ_SL_invariant γ (τ z)).trans (hJ z)), hcov, hγa, hγb,
    r, hr, hrr₀, hr1, fun q => h q + (n : ℂ), hh.add analyticOnNhd_const, ?_⟩
  intro z hz
  rw [hn, hformula z hz]
  simp only [TauCusp.correctedLogarithmWidth]
  ring

end Wikipedia.HopfProblem.SpecialPeriods
