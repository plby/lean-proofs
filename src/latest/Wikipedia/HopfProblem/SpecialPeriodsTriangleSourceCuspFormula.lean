import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCuspCoordinates

/-!
# The source quotient formula on an actual small cusp-parameter disc

For a supplied biholomorphism of the constructed compactified triangle
quotient with the Riemann sphere, taking the cusp to infinity, the proved
reciprocal-coordinate identity holds on a sufficiently high horodisc.
The exact exponential norm formula turns this into a uniform positive
radius in the original source cusp parameter.

This does not assert the existence of the supplied biholomorphism and
does not assume a pre-existing quotient coordinate or cusp formula.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.TriangleSource

attribute [local instance] triangleCompactifiedChartedSpace

/-- The normalized finite source coordinate is exactly `1728 / t(q)`
throughout an actual punctured cusp-parameter neighborhood. -/
theorem exists_cusp_formula_radius
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π triangleCuspPoint = (∞ : RiemannSphere)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ z : ℍ,
      ‖Periodic.qParam Triangle.width (z : ℂ)‖ < r₀ →
        1728 * BetaTorsor.finiteProjection π z =
          1728 / MuTorsor.CuspCoordinates.t π (Periodic.qParam Triangle.width (z : ℂ)) := by
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp
    (MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection π hπ)
  refine ⟨Triangle.cuspRadius Y, Triangle.cuspRadius_pos Y, ?_⟩
  intro z hz
  have hheight : Y < z.im := (Triangle.cuspQ_norm_lt_exp_iff Y z).mp hz
  have he := hY z hheight.le
  change MuTorsor.CuspCoordinates.t π (Periodic.qParam Triangle.width (z : ℂ)) =
    (BetaTorsor.finiteProjection π z)⁻¹ at he
  rw [he, div_inv_eq_mul]

end Wikipedia.HopfProblem.SpecialPeriods.TriangleSource
