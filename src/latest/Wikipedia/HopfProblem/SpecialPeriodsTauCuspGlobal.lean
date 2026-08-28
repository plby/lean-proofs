import Wikipedia.HopfProblem.SpecialPeriodsTauCuspWidth
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspMeromorphic
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspContinuation
import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftUpperHalfPlane

/-!
# Global modular lifts with the constructed cusp normalization

An actual meromorphic simple pole determines the normalized analytic
correction at the cusp. Its logarithmic lift supplies a genuine initial
germ for the global modular lifting theorem. The identity theorem then
extends the exact cusp formula over the entire sufficiently high source
half-plane, without a prescribed branch or a target-height assumption.
-/

open Filter Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

open CuspUniformization

private theorem exists_upperHalfPlane_qParam_small (w : ℝ) (hw : 0 < w)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ a : ℍ, ‖Function.Periodic.qParam w (a : ℂ)‖ < r := by
  obtain ⟨s, hs⟩ := logBase_set_nonempty r hr
  have hsNorm : ‖exponential s‖ < r := (CuspFamily.mem_logBase r s).mp hs
  have hsIm : 0 < s.im := upperHalfPlane_of_exponential_norm_lt_one (hsNorm.trans hr1)
  have hwsIm : 0 < ((w : ℂ) * s).im := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos hw hsIm
  refine ⟨⟨(w : ℂ) * s, hwsIm⟩, ?_⟩
  change ‖Function.Periodic.qParam w ((w : ℂ) * s)‖ < r
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  rw [qParam_eq_exponential_div, mul_div_cancel_left₀ s hwC]
  exact hsNorm

private theorem isOpen_qParam_norm_lt (w r : ℝ) :
    IsOpen {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
  isOpen_lt (Function.Periodic.continuous_qParam (h := w)).norm continuous_const

/-- The native global modular lift whose cusp expansion is derived from
the actual normalized meromorphic simple pole of the supplied function. -/
theorem exists_global_normalized_lift_of_meromorphic_cusp (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F)
    (h₃ : ∀ a : ℍ, F a = 0 →
      ∃ k : ℕ, analyticOrderAt (F ∘ ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ : ∀ a : ℍ, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F (ofComplex z) - 1728)
        (a : ℂ) = (2 * k : ℕ))
    (w : ℝ) (hw : 0 < w) (Fc : ℂ → ℂ)
    (hFc : MeromorphicAt Fc 0) (horder : meromorphicOrderAt Fc 0 = (-1 : ℤ))
    {c : ℂ} (hc : Tendsto (fun t => t * Fc t) (𝓝[≠] 0) (𝓝 c))
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hsource : ∀ z : ℍ, ‖Function.Periodic.qParam w (z : ℂ)‖ < r₀ →
      F z = Fc (Function.Periodic.qParam w (z : ℂ))) :
    ∃ τ : ℍ → ℍ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ ∧
      (∀ z : ℍ, modularJ (τ z) = F z) ∧
      ∃ r > 0, r < r₀ ∧ r < 1 ∧ ∃ h : ℂ → ℂ,
        AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧ h 0 = logarithm (1 / c) ∧
        ∀ z : ℍ, ‖Function.Periodic.qParam w (z : ℂ)‖ < r →
          (τ z : ℂ) = correctedLogarithmWidth w h (z : ℂ) := by
  obtain ⟨a, ha, ha0, hac, rF, hrF, hfactor⟩ :=
    simplePole_factorization_of_tendsto hFc horder hc
  obtain ⟨r, hr, hrr, hr1, h, hh, hh0, _, hlift⟩ :=
    exists_simplePole_logarithmic_lift_width w hw ha ha0
      (R := 1) (r₀ := min r₀ rF) zero_lt_one (lt_min hr₀ hrF)
  have hrr₀ : r < r₀ := lt_of_lt_of_le hrr (min_le_left r₀ rF)
  have hrrF : r < rF := lt_of_lt_of_le hrr (min_le_right r₀ rF)
  have hlocalJ (s : ℂ) (hs : ‖Function.Periodic.qParam w s‖ < r) :
      modularJ (ofComplex (correctedLogarithmWidth w h s)) = F (ofComplex s) := by
    have hspos : 0 < s.im := upperHalfPlane_of_qParam_norm_lt_one w hw (hs.trans hr1)
    have hqt : Function.Periodic.qParam w s ∈ Metric.ball (0 : ℂ) rF := by
      simpa only [Metric.mem_ball, dist_zero_right] using hs.trans hrrF
    have hfactorq := hfactor (Function.Periodic.qParam w s) hqt
      (Function.Periodic.qParam_ne_zero (h := w) s)
    have hsourceq : F (ofComplex s) = Fc (Function.Periodic.qParam w s) := by
      have he := hsource (ofComplex s) (by
        simpa only [ofComplex_apply_of_im_pos hspos] using hs.trans hrr₀)
      simpa only [ofComplex_apply_of_im_pos hspos] using he
    exact (hlift s hs).2.2.2.trans (hfactorq.symm.trans hsourceq.symm)
  obtain ⟨z₀, hz₀⟩ := exists_upperHalfPlane_qParam_small w hw r hr hr1
  have hJgerm : (fun s => modularJ (ofComplex (correctedLogarithmWidth w h s)))
      =ᶠ[𝓝 (z₀ : ℂ)] F ∘ ofComplex := by
    filter_upwards [(isOpen_qParam_norm_lt w r).mem_nhds hz₀] with s hs
    exact hlocalJ s hs
  obtain ⟨τ, hτ, hJ, hgerm⟩ :=
    ModularGermLift.exists_holomorphic_modularJ_lift_upperHalfPlane_extending
      F hF h₃ h₂ z₀ (correctedLogarithmWidth w h)
      (correctedLogarithmWidth_analyticAt w hh hz₀) (hlift z₀ hz₀).2.1 hJgerm
  have hformula := native_eqOn_correctedLogarithmWidth_of_eventuallyEq
    w hw hr hr1 hh hτ hz₀ hgerm
  refine ⟨τ, hτ, hJ, r, hr, hrr₀, hr1, h, hh, ?_, ?_⟩
  · simpa only [hac] using hh0
  · intro z hz
    have hzEq : (τ (ofComplex (z : ℂ)) : ℂ) = correctedLogarithmWidth w h (z : ℂ) :=
      hformula hz
    simpa only [ofComplex_apply] using hzEq

private theorem exists_simplePole_normalized_limit {Fc : ℂ → ℂ}
    (hFc : MeromorphicAt Fc 0) (horder : meromorphicOrderAt Fc 0 = (-1 : ℤ)) :
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun t => t * Fc t) (𝓝[≠] 0) (𝓝 c) := by
  obtain ⟨a, ha, ha0, r, hr, hball⟩ := simplePole_factorization hFc horder
  refine ⟨a 0, ha0, ?_⟩
  have heq : (fun t => t * Fc t) =ᶠ[𝓝[≠] (0 : ℂ)] a := by
    have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ Metric.ball 0 r :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr)
    filter_upwards [hnear, self_mem_nhdsWithin] with t ht hne
    have ht0 : t ≠ 0 := hne
    rw [hball t ht ht0]
    field_simp [ht0]
  exact ha.continuousAt.continuousWithinAt.congr' heq.symm

/-- The actual simple pole alone supplies its nonzero leading coefficient
and a global lift with the corresponding normalized cusp formula. -/
theorem exists_global_normalized_lift_of_simplePole_cusp (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F)
    (h₃ : ∀ a : ℍ, F a = 0 →
      ∃ k : ℕ, analyticOrderAt (F ∘ ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ : ∀ a : ℍ, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F (ofComplex z) - 1728)
        (a : ℂ) = (2 * k : ℕ))
    (w : ℝ) (hw : 0 < w) (Fc : ℂ → ℂ)
    (hFc : MeromorphicAt Fc 0) (horder : meromorphicOrderAt Fc 0 = (-1 : ℤ))
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hsource : ∀ z : ℍ, ‖Function.Periodic.qParam w (z : ℂ)‖ < r₀ →
      F z = Fc (Function.Periodic.qParam w (z : ℂ))) :
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun t => t * Fc t) (𝓝[≠] 0) (𝓝 c) ∧
      ∃ τ : ℍ → ℍ, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ ∧
        (∀ z : ℍ, modularJ (τ z) = F z) ∧
        ∃ r > 0, r < r₀ ∧ r < 1 ∧ ∃ h : ℂ → ℂ,
          AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧ h 0 = logarithm (1 / c) ∧
          ∀ z : ℍ, ‖Function.Periodic.qParam w (z : ℂ)‖ < r →
            (τ z : ℂ) = correctedLogarithmWidth w h (z : ℂ) := by
  obtain ⟨c, hc0, hc⟩ := exists_simplePole_normalized_limit hFc horder
  exact ⟨c, hc0, hc, exists_global_normalized_lift_of_meromorphic_cusp
    F hF h₃ h₂ w hw Fc hFc horder hc hr₀ hsource⟩

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
