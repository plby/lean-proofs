import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCuspCoordinatesCore
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrdersLocal
import Mathlib.Analysis.Meromorphic.Order

/-!
# The simple pole supplied by a genuine sphere coordinate

For a supplied biholomorphism of the actual compact triangle quotient
with the standard analytic sphere, taking the actual cusp to infinity,
the target reciprocal coordinate is an actual local biholomorphism in
the proved exponential cusp chart.  It has a simple zero, so its scaled
reciprocal has a meromorphic simple pole.  This verifies the analytic
cusp input of the global modular-lift construction.

No sphere identification is constructed or assumed to exist here: the
results apply to each actual biholomorphism supplied as an argument.
-/

noncomputable section

open Set Filter UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.TriangleSource

open Triangle MuTorsor.CuspCoordinates

attribute [local instance] triangleCompactifiedChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactified_isManifold

/-- The already constructed exponential cusp chart as an analytic partial
biholomorphism of the actual compact curve. -/
def cuspPartialDiffeomorph :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace ℂ ω where
  toPartialEquiv := (cuspFullChart width le_rfl).toPartialEquiv
  open_source := (cuspFullChart width le_rfl).open_source
  open_target := (cuspFullChart width le_rfl).open_target
  contMDiffOn_toFun := triangleCompactified_cuspChart_holomorphic
  contMDiffOn_invFun := triangleCompactified_cuspChart_symm_holomorphic

/-- The standard reciprocal sphere chart with its actual analytic inverse. -/
def sphereReciprocalPartialDiffeomorph :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) RiemannSphere ℂ ω where
  toPartialEquiv := (RiemannSphere.standardCharts.parametrization true).symm.toPartialEquiv
  open_source := (RiemannSphere.standardCharts.parametrization true).open_target
  open_target := (RiemannSphere.standardCharts.parametrization true).open_source
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (mem_range_self true))
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (mem_range_self true))

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)

/-- The actual scaled meromorphic source germ in the exponential cusp
coordinate.  Away from the cusp this is `1728` times the finite coordinate. -/
def meromorphicCuspJ (q : ℂ) : ℂ := 1728 / t π q

variable (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

/-- The actual change from the exponential cusp parameter to the target
reciprocal parameter is locally biholomorphic, including at the cusp. -/
theorem reciprocalCusp_isLocalDiffeomorphAt :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (t π) 0 := by
  have hc : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspFullChart width le_rfl).symm 0 :=
    cuspPartialDiffeomorph.symm.isLocalDiffeomorphAt _ _ _
      (Metric.mem_ball_self (cuspRadius_pos width))
  have hr : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω sphereReciprocalCoordinate
      (π ((cuspFullChart width le_rfl).symm 0)) := by
    rw [cuspFullChart_symm_zero, hπ]
    exact sphereReciprocalPartialDiffeomorph.isLocalDiffeomorphAt _ _ _
      (sphereReciprocalCoordinate_mem_source (OnePoint.infty_ne_coe (0 : ℂ)))
  have hp := hc.comp (K := 𝓘(ℂ)) (P := RiemannSphere)
    (π.isLocalDiffeomorph ((cuspFullChart width le_rfl).symm 0))
  exact hp.comp (K := 𝓘(ℂ)) (P := ℂ) hr

theorem reciprocalCusp_deriv_ne_zero : deriv (t π) 0 ≠ 0 :=
  MuTorsor.SourceOrders.deriv_ne_zero_of_isLocalDiffeomorph
    (reciprocalCusp_isLocalDiffeomorphAt π hπ)

theorem reciprocalCusp_analyticOrder : analyticOrderAt (t π) 0 = 1 :=
  MuTorsor.SourceOrders.order_eq_one_of_isLocalDiffeomorph
    (reciprocalCusp_isLocalDiffeomorphAt π hπ) (t_zero π hπ)

/-- The divided reciprocal coordinate has a nonzero value at the cusp;
its removable extension is an actual analytic unit there. -/
theorem reciprocalCusp_tDivQ_zero_ne_zero : tDivQ π 0 ≠ 0 := by
  simpa only [tDivQ, dslope_same] using reciprocalCusp_deriv_ne_zero π hπ

theorem meromorphicCuspJ_meromorphicAt : MeromorphicAt (meromorphicCuspJ π) 0 :=
  analyticAt_const.meromorphicAt.div (t_analyticAt_zero π hπ).meromorphicAt

/-- The actual cusp source germ has order exactly minus one; this is a
proved simple pole, not a supplied asymptotic or a pole-order hypothesis. -/
theorem meromorphicCuspJ_order : meromorphicOrderAt (meromorphicCuspJ π) 0 = (-1 : ℤ) := by
  change meromorphicOrderAt ((fun _ : ℂ => (1728 : ℂ)) / t π) 0 = _
  rw [meromorphicOrderAt_div analyticAt_const.meromorphicAt
    (t_analyticAt_zero π hπ).meromorphicAt,
    (t_analyticAt_zero π hπ).meromorphicOrderAt_eq, reciprocalCusp_analyticOrder π hπ]
  norm_num [meromorphicOrderAt_const]

end Wikipedia.HopfProblem.SpecialPeriods.TriangleSource
