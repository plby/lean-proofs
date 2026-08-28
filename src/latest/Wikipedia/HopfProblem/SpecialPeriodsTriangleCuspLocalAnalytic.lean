import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspBall
import Wikipedia.HopfProblem.SpecialPeriodsModularLocalChartsInverse
import Wikipedia.HopfProblem.CuspPuncturedCovering

/-!
# Local analytic inverse charts for the cusp exponential

The proved nonzero complex derivative of the cusp coordinate gives actual
analytic inverse charts.  Composing with the standard upper-half-plane
chart and then restricting to the specified open subsets proves that both
the cusp exponential and its horodisc restriction are local biholomorphisms
for their existing complex manifold structures.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

private theorem upperHalfPlaneCoe_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (UpperHalfPlane.coe : ℍ → ℂ) := by
  let Φ : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℍ ℂ ω :=
    { toPartialEquiv := UpperHalfPlane.ofComplex.symm.toPartialEquiv
      open_source := UpperHalfPlane.ofComplex.symm.open_source
      open_target := UpperHalfPlane.ofComplex.symm.open_target
      contMDiffOn_toFun := UpperHalfPlane.contMDiff_coe.contMDiffOn
      contMDiffOn_invFun := by
        intro w hw
        have he : ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) = w :=
          UpperHalfPlane.ofComplex.left_inv hw
        have hwim : 0 < w.im := by
          rw [← he]
          exact (UpperHalfPlane.ofComplex w).im_pos
        exact (UpperHalfPlane.contMDiffAt_ofComplex hwim).contMDiffWithinAt }
  intro z
  refine ⟨Φ, ?_, fun _ _ => rfl⟩
  exact mem_univ z

private theorem cuspQ_coordinate_isLocalDiffeomorphAt (z : ℍ) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspQ ∘ UpperHalfPlane.ofComplex) (z : ℂ) := by
  have ha : AnalyticAt ℂ (cuspQ ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
    (UpperHalfPlane.contMDiffAt_iff.mp (cuspQ_holomorphic z)).analyticAt
  obtain ⟨e, hz, he, hforward, hinverse⟩ :=
    exists_analytic_openPartialHomeomorph ha (cuspQ_deriv_ne_zero z)
  refine ⟨{
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := (hforward.contDiffOn e.open_source.uniqueDiffOn).contMDiffOn
    contMDiffOn_invFun := (hinverse.contDiffOn e.open_target.uniqueDiffOn).contMDiffOn }, hz, ?_⟩
  intro w _
  exact (he w).symm

/-- The actual normalized cusp exponential is everywhere locally
biholomorphic from the upper half-plane to the complex line. -/
theorem cuspQ_isLocalDiffeomorph : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω cuspQ := by
  intro z
  have h := (upperHalfPlaneCoe_isLocalDiffeomorph z).comp (K := 𝓘(ℂ)) (P := ℂ)
    (cuspQ_coordinate_isLocalDiffeomorphAt z)
  simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply] using h

/-- Restricting the source to any horodisc and the target to its precise
punctured ball preserves the genuine analytic inverse charts. -/
theorem cuspQHorodisc_isLocalDiffeomorph (Y : ℝ) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (cuspQHorodisc Y) := by
  intro z
  exact isLocalDiffeomorphAt_restrictOpens 𝓘(ℂ) 𝓘(ℂ)
    (cuspQ_isLocalDiffeomorph (z : ℍ)) (horodisc Y) (puncturedCuspBall Y)
    (fun w hw => (cuspQ_mem_puncturedCuspBall_iff Y w).mpr hw) z.property

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
