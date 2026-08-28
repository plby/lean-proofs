import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Holomorphic inverses of planar local homeomorphisms

A holomorphic open partial homeomorphism has a holomorphic inverse for its
existing source and target.  No nonvanishing-derivative hypothesis is needed.
The derivative is analytic, so its zeros are locally isolated unless it
vanishes on a neighborhood.  The latter case contradicts local injectivity.
The inverse is therefore holomorphic on a punctured neighborhood, and its
continuity removes the remaining singularity.
-/

noncomputable section

open Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

/-- The critical points of a holomorphic open partial homeomorphism are
locally isolated.  This intermediate statement does not assume that the
derivative at the center is nonzero. -/
theorem eventually_deriv_ne_zero_of_differentiableOn
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) {a : ℂ} (ha : a ∈ e.source) :
    ∀ᶠ z in 𝓝[≠] a, deriv e z ≠ 0 := by
  have hda : AnalyticAt ℂ (deriv e) a :=
    (he.analyticAt (e.open_source.mem_nhds ha)).deriv
  rcases hda.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
  · exfalso
    have hnear : ∀ᶠ z in 𝓝 a, z ∈ e.source ∧ deriv e z = 0 := by
      filter_upwards [e.open_source.mem_nhds ha, hzero] with z hz hdz
      exact ⟨hz, hdz⟩
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
    have hballSource : ball a r ⊆ e.source := fun z hz => (hball hz).1
    have hconstant : ∀ z ∈ ball a r, e z = e a := by
      intro z hz
      exact isOpen_ball.is_const_of_deriv_eq_zero isPreconnected_ball
        (he.mono hballSource) (fun w hw => (hball hw).2) hz (mem_ball_self hr)
    have hballNhds : ∀ᶠ z in 𝓝 a, z ∈ ball a r := ball_mem_nhds a hr
    have hballPunctured : ∀ᶠ z in 𝓝[≠] a, z ∈ ball a r :=
      hballNhds.filter_mono nhdsWithin_le_nhds
    obtain ⟨z, hz, hza⟩ :=
      (hballPunctured.and (self_mem_nhdsWithin : ∀ᶠ z in 𝓝[≠] a, z ≠ a)).exists
    exact hza (e.injOn (hballSource hz) ha (hconstant z hz))
  · exact hnonzero

/-- The inverse of a holomorphic planar open partial homeomorphism is
holomorphic, without any assumption about its derivative. -/
theorem differentiableOn_symm_of_differentiableOn
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) :
    DifferentiableOn ℂ e.symm e.target := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  apply AnalyticAt.differentiableAt
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hnonzero := eventually_deriv_ne_zero_of_differentiableOn e he (e.map_target hw)
    rw [eventually_nhdsWithin_iff] at hnonzero
    have hnear := (e.continuousAt_symm hw).tendsto.eventually hnonzero
    rw [eventually_nhdsWithin_iff]
    filter_upwards [e.open_target.mem_nhds hw, hnear] with z hz hdz hzw
    have hinvNe : e.symm z ≠ e.symm w := fun h => hzw (e.symm.injOn hz hw h)
    exact (e.hasDerivAt_symm hz (hdz hinvNe)
      (he.hasDerivAt (e.open_source.mem_nhds (e.map_target hz)))).differentiableAt
  · exact e.continuousAt_symm hw

/-- The same inverse theorem expressed in terms of analytic functions on
neighborhoods of all points of the target. -/
theorem analyticOnNhd_symm_of_differentiableOn
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) :
    AnalyticOnNhd ℂ e.symm e.target :=
  (differentiableOn_symm_of_differentiableOn e he).analyticOnNhd e.open_target

/-- Nonvanishing of the derivative is a consequence, not a hypothesis:
differentiate the actual inverse identity after proving inverse holomorphy. -/
theorem deriv_ne_zero_of_differentiableOn
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) {a : ℂ} (ha : a ∈ e.source) :
    deriv e a ≠ 0 := by
  intro hzero
  have hd := he.hasDerivAt (e.open_source.mem_nhds ha)
  have hdi := (differentiableOn_symm_of_differentiableOn e he).hasDerivAt
    (e.open_target.mem_nhds (e.map_source ha))
  have hcomp := hdi.comp a hd
  rw [hzero, mul_zero] at hcomp
  have hleft : (e.symm ∘ e) =ᶠ[𝓝 a] id := e.eventually_left_inverse ha
  have hid := hcomp.congr_of_eventuallyEq hleft.symm
  exact zero_ne_one (hid.unique (hasDerivAt_id a))

end Wikipedia.HopfProblem.TriangleUniformizationGluing
