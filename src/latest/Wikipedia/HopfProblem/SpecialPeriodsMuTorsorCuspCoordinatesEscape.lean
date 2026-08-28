import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorBase
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspEscape
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-! # Escape in the actual finite cusp coordinate

As the imaginary part of an upper-half-plane point tends to infinity,
its image in the constructed compact triangle quotient tends to the added
cusp.  A supplied biholomorphism taking that cusp to the point at infinity
therefore makes the actual finite orbit coordinate escape every bounded
subset of the complex plane.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane Bornology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.CuspCoordinates

attribute [local instance] triangleCompactifiedChartedSpace

/-- The upper-half-plane height filter eventually lies in every actual
horodisc, with no restriction on the real part. -/
theorem eventually_mem_horodisc (Y : ℝ) :
    ∀ᶠ z in atImInfty, z ∈ Triangle.horodisc Y := by
  apply (UpperHalfPlane.atImInfty_mem _).mpr
  exact ⟨Y + 1, fun _ hz => lt_of_lt_of_le (lt_add_one Y) hz⟩

/-- The actual compactified orbit projection tends to the actual added
cusp along the upper-half-plane height filter. -/
theorem compactifiedProjection_tendsto_cusp :
    Tendsto triangleCompactifiedProjection atImInfty (𝓝 triangleCuspPoint) := by
  rw [Triangle.cuspNeighborhood_basis.tendsto_right_iff]
  intro Y _
  filter_upwards [eventually_mem_horodisc Y] with z hz
  change triangleOpenInclusion (triangleOrbitProjection z) ∈ Triangle.cuspNeighborhood Y
  apply (Triangle.openInclusion_mem_cuspNeighborhood Y _).mpr
  exact ⟨z, hz, rfl⟩

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

/-- The supplied sphere map carries actual cusp escape to convergence to
the point at infinity of the Riemann sphere. -/
theorem sphereProjection_tendsto_infty :
    Tendsto (π ∘ triangleCompactifiedProjection) atImInfty (𝓝 (∞ : RiemannSphere)) := by
  have h := π.continuous.continuousAt.tendsto.comp compactifiedProjection_tendsto_cusp
  simpa only [hπ] using h

/-- The finite coordinate agrees with the actual sphere-valued projection. -/
@[simp] theorem finiteProjection_coe (z : ℍ) :
    (BetaTorsor.finiteProjection π z : RiemannSphere) = π (triangleCompactifiedProjection z) :=
  BetaTorsor.finiteOrbitCoordinate_coe π hπ (triangleOrbitProjection z)

/-- Convergence to infinity in the standard sphere is escape from every
bounded set in its finite complex chart. -/
theorem finiteProjection_tendsto_cobounded :
    Tendsto (BetaTorsor.finiteProjection π) atImInfty (cobounded ℂ) := by
  have hc : comap (fun z : ℂ => (z : RiemannSphere)) (𝓝 (∞ : RiemannSphere)) =
      cobounded ℂ := by
    simpa only [coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
      (OnePoint.comap_coe_nhds_infty (X := ℂ))
  rw [← hc, tendsto_comap_iff]
  simpa only [Function.comp_def, finiteProjection_coe π hπ] using
    sphereProjection_tendsto_infty π hπ

/-- The norm of the actual finite projection tends to positive infinity. -/
theorem finiteProjection_norm_tendsto_atTop :
    Tendsto (fun z : ℍ => ‖BetaTorsor.finiteProjection π z‖) atImInfty atTop :=
  tendsto_norm_cobounded_atTop.comp (finiteProjection_tendsto_cobounded π hπ)

theorem eventually_lt_norm_finiteProjection (R : ℝ) :
    ∀ᶠ z in atImInfty, R < ‖BetaTorsor.finiteProjection π z‖ :=
  (finiteProjection_norm_tendsto_atTop π hπ).eventually_gt_atTop R

theorem finiteProjection_eventually_ne_zero :
    ∀ᶠ z in atImInfty, BetaTorsor.finiteProjection π z ≠ 0 := by
  filter_upwards [eventually_lt_norm_finiteProjection π hπ 0] with z hz
  exact norm_pos_iff.mp hz

/-- The reciprocal finite coordinate tends to zero through nonzero values. -/
theorem finiteProjection_inv_tendsto_zero :
    Tendsto (fun z : ℍ => (BetaTorsor.finiteProjection π z)⁻¹)
      atImInfty (𝓝[≠] (0 : ℂ)) :=
  tendsto_inv₀_cobounded'.comp (finiteProjection_tendsto_cobounded π hπ)

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.CuspCoordinates
