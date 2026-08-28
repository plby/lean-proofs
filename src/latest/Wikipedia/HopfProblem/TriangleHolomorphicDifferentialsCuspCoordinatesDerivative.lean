import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsGeometry
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCuspCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsTriangleSourceCusp
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Differentiating the actual reciprocal cusp coordinate

An identity on a sufficiently high horodisc is an identity of local germs
at every sufficiently high point, and hence may be differentiated there.
Applying this to the actual reciprocal sphere coordinate gives the exact
derivative of the finite source coordinate in the exponential parameter.
The divided reciprocal coordinate and its derivative are actual analytic
units, by the previously proved local biholomorphism at the filled cusp.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleCompactifiedChartedSpace

/-- Equality on a high horodisc is eventually equality of ordinary local germs. -/
theorem eventuallyEq_nhds_of_eventuallyEq_atImInfty {α : Type*} {f g : ℍ → α}
    (hfg : f =ᶠ[atImInfty] g) :
    ∀ᶠ z in atImInfty, f =ᶠ[𝓝 z] g := by
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem {z | f z = g z}).mp hfg
  filter_upwards [MuTorsor.CuspCoordinates.eventually_mem_horodisc Y] with z hz
  filter_upwards [(isOpen_lt continuous_const UpperHalfPlane.continuous_im).mem_nhds hz]
    with w hw
  exact hY w hw.le

/-- The scalar derivative respects eventual equality on high horodiscs. -/
theorem scalarDeriv_eventuallyEq_of_eventuallyEq {f g : ℍ → ℂ}
    (hfg : f =ᶠ[atImInfty] g) :
    scalarDeriv f =ᶠ[atImInfty] scalarDeriv g := by
  filter_upwards [eventuallyEq_nhds_of_eventuallyEq_atImInfty hfg] with z hz
  have ho : Tendsto UpperHalfPlane.ofComplex (𝓝 (z : ℂ)) (𝓝 z) := by
    simpa only [UpperHalfPlane.ofComplex_apply] using
      (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) z.im_pos).continuousAt.tendsto
  exact (hz.comp_tendsto ho).deriv_eq

/-- The exact nonzero derivative coefficient of the original exponential parameter. -/
def cuspDerivativeScale : ℂ := 2 * Real.pi * Complex.I / width

theorem cuspDerivativeScale_ne_zero : cuspDerivativeScale ≠ 0 :=
  div_ne_zero Complex.two_pi_I_ne_zero (Complex.ofReal_ne_zero.mpr width_ne_zero)

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
    TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

/-- The derivative of the actual reciprocal cusp coordinate is analytic at zero. -/
theorem reciprocalCusp_deriv_analyticAt :
    AnalyticAt ℂ (deriv (MuTorsor.CuspCoordinates.t π)) 0 :=
  (MuTorsor.CuspCoordinates.t_analyticAt_zero π hπ).deriv

/-- The exact finite-coordinate derivative in the actual exponential cusp parameter. -/
theorem finiteProjection_scalarDeriv_cusp :
    ∀ᶠ z in atImInfty,
      scalarDeriv (BetaTorsor.finiteProjection π) z =
        -cuspDerivativeScale * deriv (MuTorsor.CuspCoordinates.t π) (cuspQ z) /
          (cuspQ z * MuTorsor.CuspCoordinates.tDivQ π (cuspQ z) ^ 2) := by
  have he : BetaTorsor.finiteProjection π =ᶠ[atImInfty]
      fun z => (MuTorsor.CuspCoordinates.t π (cuspQ z))⁻¹ := by
    filter_upwards [MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection π hπ] with z hz
    simpa only [inv_inv] using (congrArg (fun w : ℂ => w⁻¹) hz).symm
  have hq : Tendsto cuspQ atImInfty (𝓝 (0 : ℂ)) :=
    cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds
  have ht : ∀ᶠ z in atImInfty,
      AnalyticAt ℂ (MuTorsor.CuspCoordinates.t π) (cuspQ z) :=
    hq.eventually (MuTorsor.CuspCoordinates.t_analyticAt_zero π hπ).eventually_analyticAt
  have hU : ∀ᶠ z in atImInfty,
      MuTorsor.CuspCoordinates.tDivQ π (cuspQ z) ≠ 0 :=
    hq.eventually ((MuTorsor.CuspCoordinates.tDivQ_analyticAt_zero π hπ).continuousAt.eventually_ne
      (TriangleSource.reciprocalCusp_tDivQ_zero_ne_zero π hπ))
  filter_upwards [scalarDeriv_eventuallyEq_of_eventuallyEq he, ht, hU] with z hz htz hUz
  have htz0 : MuTorsor.CuspCoordinates.t π (cuspQ z) ≠ 0 := by
    rw [MuTorsor.CuspCoordinates.t_eq_mul_tDivQ π hπ]
    exact mul_ne_zero (cuspQ_ne_zero z) hUz
  have hd : HasDerivAt
      (fun w : ℂ => (MuTorsor.CuspCoordinates.t π (cuspQ (UpperHalfPlane.ofComplex w)))⁻¹)
      (-(deriv (MuTorsor.CuspCoordinates.t π) (cuspQ z) *
        (cuspQ z * cuspDerivativeScale)) /
          (MuTorsor.CuspCoordinates.t π (cuspQ z)) ^ 2) (z : ℂ) := by
    have hout : HasDerivAt (MuTorsor.CuspCoordinates.t π)
        (deriv (MuTorsor.CuspCoordinates.t π) (cuspQ z))
        ((cuspQ ∘ UpperHalfPlane.ofComplex) (z : ℂ)) := by
      simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
        htz.differentiableAt.hasDerivAt
    have hcomp := hout.comp (z : ℂ)
      (cuspQ_hasStrictDerivAt z).hasDerivAt
    have hn : MuTorsor.CuspCoordinates.t π
        (cuspQ (UpperHalfPlane.ofComplex (z : ℂ))) ≠ 0 := by
      simpa only [UpperHalfPlane.ofComplex_apply] using htz0
    simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply, cuspDerivativeScale] using!
      hcomp.inv hn
  rw [hz]
  change deriv (fun w : ℂ =>
    (MuTorsor.CuspCoordinates.t π (cuspQ (UpperHalfPlane.ofComplex w)))⁻¹) (z : ℂ) = _
  rw [hd.deriv, MuTorsor.CuspCoordinates.t_eq_mul_tDivQ π hπ]
  field_simp [cuspQ_ne_zero z, hUz]

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
