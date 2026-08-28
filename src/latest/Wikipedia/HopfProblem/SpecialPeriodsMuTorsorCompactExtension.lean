import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCompactExtensionBasic
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCompactExtensionCusp

/-!
# Vanishing from an analytic cusp germ on the actual compact quotient

An eventual identity on high points of the upper half-plane is converted to
an identity on a genuine cusp neighbourhood of the quotient.  The explicit
one-point extension is therefore holomorphic on the actual compact curve.
It is constant, and it is zero when the analytic cusp germ vanishes at zero.
-/

noncomputable section

open Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

variable (f : TriangleOrbitSpace → ℂ) (g : ℂ → ℂ)

/-- The eventual upper-half-plane formula proves holomorphy of the literal
one-point extension in the constructed compact complex atlas. -/
theorem compactExtension_holomorphic_of_eventually_cusp
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : AnalyticAt ℂ g 0)
    (h : ∀ᶠ z in atImInfty, f (triangleOrbitProjection z) = g (Triangle.cuspQ z)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f (g 0)) := by
  obtain ⟨Y, _, hY⟩ := exists_cuspImage_eq_of_eventually_atImInfty h
  exact compactExtension_holomorphic_of_cuspImage f g Y hf hg hY

theorem zeroCompactExtension_holomorphic_of_eventually_cusp
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (h : ∀ᶠ z in atImInfty, f (triangleOrbitProjection z) = g (Triangle.cuspQ z)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f 0) := by
  simpa only [hg0] using compactExtension_holomorphic_of_eventually_cusp f g hf hg h

/-- A holomorphic function with an analytic cusp germ is the constant given
by that germ's value at zero.  Compact extension is constructed in the proof. -/
theorem eq_const_of_eventually_cusp
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : AnalyticAt ℂ g 0)
    (h : ∀ᶠ z in atImInfty, f (triangleOrbitProjection z) = g (Triangle.cuspQ z)) :
    ∀ q, f q = g 0 := by
  obtain ⟨Y, _, hY⟩ := exists_cuspImage_eq_of_eventually_atImInfty h
  exact eq_const_of_cuspImage f g Y hf hg hY

/-- The global vanishing conclusion follows from the actual compact complex
curve, without assuming any compact extension or projective-line model. -/
theorem eq_zero_of_eventually_cusp
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (h : ∀ᶠ z in atImInfty, f (triangleOrbitProjection z) = g (Triangle.cuspQ z)) :
    f = 0 := by
  funext q
  exact (eq_const_of_eventually_cusp f g hf hg h q).trans hg0

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
