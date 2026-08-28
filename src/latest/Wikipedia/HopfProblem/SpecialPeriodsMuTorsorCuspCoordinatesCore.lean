import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCoverSphere
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The actual reciprocal coordinate in the filled cusp chart

The coordinate is the composition of the genuine inverse cusp chart, the
supplied normalized sphere identification, and the standard reciprocal
sphere chart. Its zero at the cusp makes division by the source cusp
parameter removable, with the extension given by the actual divided slope.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.CuspCoordinates

open Triangle

attribute [local instance] triangleCompactifiedChartedSpace

/-- The standard reciprocal affine chart on the actual analytic sphere. -/
def sphereReciprocalCoordinate : RiemannSphere → ℂ :=
  (RiemannSphere.standardCharts.parametrization true).symm

theorem sphereReciprocalCoordinate_mem_source {p : RiemannSphere}
    (hp : p ≠ ((0 : ℂ) : RiemannSphere)) :
    p ∈ (RiemannSphere.standardCharts.parametrization true).target := by
  rw [TwoAffineCharts.parametrization_target]
  change p ∈ range RiemannSphere.standardCharts.right
  rw [RiemannSphere.standardCharts.range_right]
  exact hp

@[simp] theorem sphereReciprocalCoordinate_infty :
    sphereReciprocalCoordinate (∞ : RiemannSphere) = 0 := by
  have h := RiemannSphere.standardCharts.parametrization_symm_apply true (0 : ℂ)
  change sphereReciprocalCoordinate (RiemannSphere.infinityParametrization 0) = 0 at h
  simpa only [RiemannSphere.infinityParametrization_zero] using h

theorem sphereReciprocalCoordinate_coe {z : ℂ} (hz : z ≠ 0) :
    sphereReciprocalCoordinate (z : RiemannSphere) = z⁻¹ := by
  have he : RiemannSphere.infinityParametrization z⁻¹ = (z : RiemannSphere) := by
    rw [RiemannSphere.infinityParametrization_of_ne (inv_ne_zero hz), inv_inv]
  have h := RiemannSphere.standardCharts.parametrization_symm_apply true z⁻¹
  change sphereReciprocalCoordinate (RiemannSphere.infinityParametrization z⁻¹) = z⁻¹ at h
  simpa only [he] using h

theorem sphereReciprocalCoordinate_holomorphicAt {p : RiemannSphere}
    (hp : p ≠ ((0 : ℂ) : RiemannSphere)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereReciprocalCoordinate p := by
  apply contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (mem_range_self true))
  exact sphereReciprocalCoordinate_mem_source hp

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)

/-- The actual target reciprocal coordinate as a function of the source
exponential cusp coordinate, defined on the ambient complex plane. -/
def t (q : ℂ) : ℂ :=
  sphereReciprocalCoordinate (π ((cuspFullChart width le_rfl).symm q))

/-- The canonical removable extension of `t(q) / q` at zero. -/
def tDivQ : ℂ → ℂ := dslope (t π) 0

variable (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

@[simp] theorem t_zero : t π 0 = 0 := by
  rw [t, cuspFullChart_symm_zero, hπ, sphereReciprocalCoordinate_infty]

theorem t_holomorphicAt_zero : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (t π) 0 := by
  have hC : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspFullChart width le_rfl).symm (0 : ℂ) :=
    triangleCompactified_cuspChart_symm_holomorphic.contMDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (cuspRadius_pos width)))
  have hR : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereReciprocalCoordinate
      (π ((cuspFullChart width le_rfl).symm 0)) := by
    rw [cuspFullChart_symm_zero, hπ]
    exact sphereReciprocalCoordinate_holomorphicAt (OnePoint.infty_ne_coe (0 : ℂ))
  exact hR.comp 0 (π.contMDiffAt.comp 0 hC)

theorem t_analyticAt_zero : AnalyticAt ℂ (t π) 0 :=
  (t_holomorphicAt_zero π hπ).contDiffAt.analyticAt

theorem tDivQ_analyticAt_zero : AnalyticAt ℂ (tDivQ π) 0 :=
  (t_analyticAt_zero π hπ).hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

/-- The factorization is an exact identity of functions, not just an
asymptotic expansion. -/
theorem t_eq_mul_tDivQ (q : ℂ) : t π q = q * tDivQ π q := by
  simpa only [tDivQ, sub_zero, t_zero π hπ, smul_eq_mul] using
    (sub_smul_dslope (t π) 0 q).symm

theorem tDivQ_eq_div {q : ℂ} (hq : q ≠ 0) : tDivQ π q = t π q / q := by
  rw [t_eq_mul_tDivQ π hπ q, mul_div_cancel_left₀ _ hq]

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.CuspCoordinates
