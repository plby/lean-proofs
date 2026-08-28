import Wikipedia.HopfProblem.SpecialPeriodsTriangleSourceCusp
import Wikipedia.HopfProblem.SpecialPeriodsTriangleSourceCuspFormula
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrders
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauConstruction

/-!
# Constructing the special tau from a normalized actual sphere equivalence

A supplied normalized biholomorphism of the actual compact triangle
quotient determines a genuine invariant source function.  Its branching
orders and its simple cusp pole have already been proved from the actual
quotient charts.  Applying the global modular construction therefore
produces a holomorphic tau with the source's generator equations and
analytic cusp expansion, without assuming any properties of such a tau.

The sphere equivalence remains an explicit argument; its existence is
not asserted by this file.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.TriangleSource

open Triangle MuTorsor.SourceOrders

attribute [local instance] triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))

include hπ h₀ h₁ in
/-- All analytic source data for tau are derived from the supplied genuine
normalized sphere equivalence, including the exact orders at every fibre. -/
theorem exists_tau_of_normalized_sphere_equivalence :
    ∃ τ : ℍ → ℍ, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ ∧
      (∀ z : ℍ, modularJ (τ z) = sourceJ π z) ∧ TauCovariant τ ∧
      τ centerOne = rhoPoint ∧ τ centerTwo = UpperHalfPlane.I ∧
      ∃ r > 0, r < 1 ∧ ∃ h : ℂ → ℂ,
        AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
        ∀ z : ℍ, ‖Function.Periodic.qParam width (z : ℂ)‖ < r →
          (τ z : ℂ) = TauCusp.correctedLogarithmWidth width h (z : ℂ) := by
  have h₃ : ∀ z : ℍ, sourceJ π z = 0 →
      ∃ k : ℕ, analyticOrderAt (sourceJ π ∘ ofComplex) (z : ℂ) = (3 * k : ℕ) := by
    intro z hz
    exact ⟨1, by simpa using sourceJ_order_of_eq_zero π hπ h₀ z hz⟩
  have h₂ : ∀ z : ℍ, sourceJ π z = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun w => sourceJ π (ofComplex w) - 1728)
        (z : ℂ) = (2 * k : ℕ) := by
    intro z hz
    exact ⟨2, by simpa using sourceJ_sub_1728_order_of_eq π hπ h₁ z hz⟩
  have hG₁ : ∀ z : ℍ, sourceJ π (generatorOneSL • z) = sourceJ π z := by
    intro z
    simpa only [triangleGeometricRepresentation_generator₁_apply] using
      sourceJ_invariant π triangleGenerator₁ z
  have hG₂ : ∀ z : ℍ, sourceJ π (generatorTwoSL • z) = sourceJ π z := by
    intro z
    simpa only [triangleGeometricRepresentation_generator₂_apply] using
      sourceJ_invariant π triangleGenerator₂ z
  obtain ⟨r₀, hr₀, hsource⟩ := exists_cusp_formula_radius π hπ
  obtain ⟨τ, hτ, hJ, hcov, ha, hb, r, hr, _, hr1, h, hh, hformula⟩ :=
    exists_covariant_tau_of_triangle_source (sourceJ π)
      ((sourceJ_holomorphic π hπ).mdifferentiable (by simp)) h₃ h₂ hG₁ hG₂
      (sourceJ_order_centerOne π hπ h₀) (sourceJ_sub_1728_order_centerTwo π hπ h₁)
      (meromorphicCuspJ π) (meromorphicCuspJ_meromorphicAt π hπ)
      (meromorphicCuspJ_order π hπ) hr₀ hsource
  exact ⟨τ, hτ, hJ, hcov, ha, hb, r, hr, hr1, h, hh, hformula⟩

/-- The constructed normalized holomorphic tau for a supplied actual
normalized sphere equivalence. -/
def tauOfSphere : ℍ → ℍ :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose

theorem tauOfSphere_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (tauOfSphere π hπ h₀ h₁) :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.1

theorem tauOfSphere_modular (z : ℍ) :
    modularJ (tauOfSphere π hπ h₀ h₁ z) = 1728 * BetaTorsor.finiteProjection π z :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.2.1 z

theorem tauOfSphere_covariant : TauCovariant (tauOfSphere π hπ h₀ h₁) :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.2.2.1

@[simp] theorem tauOfSphere_centerOne : tauOfSphere π hπ h₀ h₁ centerOne = rhoPoint :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.2.2.2.1

@[simp] theorem tauOfSphere_centerTwo : tauOfSphere π hπ h₀ h₁ centerTwo = UpperHalfPlane.I :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.2.2.2.2.1

theorem tauOfSphere_cusp :
    ∃ r > 0, r < 1 ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
      ∀ z : ℍ, ‖Function.Periodic.qParam width (z : ℂ)‖ < r →
        (tauOfSphere π hπ h₀ h₁ z : ℂ) = TauCusp.correctedLogarithmWidth width h (z : ℂ) :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.2.2.2.2.2

/-- The exponential of the actual holomorphic cusp correction. -/
def cuspCorrectionUnit (h : ℂ → ℂ) (q : ℂ) : ℂ := CuspUniformization.exponential (h q)

theorem cuspCorrectionUnit_analyticOnNhd {h : ℂ → ℂ} {r : ℝ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) :
    AnalyticOnNhd ℂ (cuspCorrectionUnit h) (Metric.ball 0 r) := by
  intro q hq
  exact CuspUniformization.exponential_holomorphic.contDiffAt.analyticAt.comp (hh q hq)

@[simp] theorem cuspCorrectionUnit_ne_zero (h : ℂ → ℂ) (q : ℂ) :
    cuspCorrectionUnit h q ≠ 0 := CuspUniformization.exponential_ne_zero _

/-- The modular cusp parameter is the actual source cusp parameter times
a genuinely analytic unit at the added point. -/
theorem tauOfSphere_cusp_unit :
    ∃ r > 0, ∃ u : ℂ → ℂ, AnalyticOnNhd ℂ u (Metric.ball 0 r) ∧ u 0 ≠ 0 ∧
      ∀ z : ℍ, ‖Function.Periodic.qParam width (z : ℂ)‖ < r →
        Function.Periodic.qParam 1 (tauOfSphere π hπ h₀ h₁ z : ℂ) =
          Function.Periodic.qParam width (z : ℂ) *
            u (Function.Periodic.qParam width (z : ℂ)) := by
  obtain ⟨r, hr, _, h, hh, hformula⟩ := tauOfSphere_cusp π hπ h₀ h₁
  refine ⟨r, hr, cuspCorrectionUnit h, cuspCorrectionUnit_analyticOnNhd hh,
    cuspCorrectionUnit_ne_zero h 0, ?_⟩
  intro z hz
  rw [← TauCusp.exponential_eq_qParam_one, hformula z hz]
  exact TauCusp.correctedLogarithmWidth_exponential width h z

end Wikipedia.HopfProblem.SpecialPeriods.TriangleSource
