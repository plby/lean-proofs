import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegularCoefficient
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspScalarBasic

/-!
# The actual regular canonical coefficient in cusp coordinates

The regular-locus finite coordinate and the original upper-half-plane
source coordinate agree through the actual normalized sphere map. Their
native chart inverses have the same complex coordinate on their targets,
so their scalar derivatives agree. The derived cusp expression therefore
applies to the actual regular canonical coefficient on a full high horodisc.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspScalar

open Triangle TriangleHolomorphicDifferentials TrianglePeriodFamily
open TrianglePeriodFamily.Canonical

/-- Both definitions are the finite coordinate of the same actual normalized sphere map. -/
theorem upstairsCoordinate_eq_sourceCoordinate (z : TriangleRegularPoint) :
    GlobalRegular.upstairsCoordinate z = specialSourceCoordinate z.val := by
  apply OnePoint.coe_injective
  exact (GlobalRegular.upstairsCoordinate_coe z).trans
    (BetaTorsor.finiteOrbitCoordinate_coe triangleSphereUniformization
      triangleSphereUniformization_cusp (triangleOrbitProjection z.val)).symm

/-- A native regular chart inverse has exactly the original upper-half-plane point. -/
theorem regularChart_inverse_base (a : TriangleRegularPoint) {w : ℂ}
    (hw : w ∈ (chartAt ℂ a).target) :
    ((chartAt ℂ a).symm w).val = UpperHalfPlane.ofComplex w := by
  have hc : (((chartAt ℂ a).symm w).val : ℂ) = w := by
    simpa only [regularPoint_chart_apply] using (chartAt ℂ a).right_inv hw
  simpa only [UpperHalfPlane.ofComplex_apply] using congrArg UpperHalfPlane.ofComplex hc

/-- The two actual ambient expressions agree throughout the native chart target. -/
theorem chartCoordinate_eq_sourceCoordinate (a : TriangleRegularPoint) {w : ℂ}
    (hw : w ∈ (chartAt ℂ a).target) :
    GlobalRegular.chartCoordinate a w = specialSourceCoordinate (UpperHalfPlane.ofComplex w) := by
  change GlobalRegular.upstairsCoordinate ((chartAt ℂ a).symm w) = _
  rw [upstairsCoordinate_eq_sourceCoordinate, regularChart_inverse_base a hw]

theorem chartCoordinate_eventuallyEq_sourceCoordinate (z : TriangleRegularPoint) :
    GlobalRegular.chartCoordinate z =ᶠ[𝓝 (z.val : ℂ)]
      (specialSourceCoordinate ∘ UpperHalfPlane.ofComplex) := by
  filter_upwards [(chartAt ℂ z).open_target.mem_nhds
    (GlobalRegular.regularPoint_chart_self_mem_target z)] with w hw
  exact chartCoordinate_eq_sourceCoordinate z hw

/-- The native regular-base derivative is the original upper-half-plane scalar derivative. -/
theorem coordinateDerivative_eq_scalarDeriv (z : TriangleRegularPoint) :
    GlobalRegular.coordinateDerivative z = scalarDeriv specialSourceCoordinate z.val :=
  (chartCoordinate_eventuallyEq_sourceCoordinate z).deriv_eq

/-- The coefficient of the actual regular canonical form is literally the
source-coordinate derivative divided by the constructed modular generator. -/
theorem regularCoefficient_eq_scalarDeriv_div_generator (z : TriangleRegularPoint) :
    GlobalRegular.regularCoefficient z =
      scalarDeriv specialSourceCoordinate z.val / GlobalGenerator.generator z.val := by
  change GlobalRegular.coordinateDerivative z / GlobalGenerator.generator z.val = _
  rw [coordinateDerivative_eq_scalarDeriv]

/-- The actual regular coefficient agrees with the actual cusp germ high
in the cusp, uniformly over every proof of regular-locus membership. -/
theorem regularCoefficient_eventually :
    ∀ᶠ z in atImInfty, ∀ hz : z ∈ triangleRegularLocus,
      GlobalRegular.regularCoefficient ⟨z, hz⟩ = coefficientGerm (cuspQ z) := by
  filter_upwards [scalarDeriv_div_generator_eventually] with z hz
  intro hreg
  rw [regularCoefficient_eq_scalarDeriv_div_generator]
  exact hz

/-- There is an actual high horodisc on which every native regular point
has the displayed canonical coefficient, with no scalar comparison premise. -/
theorem regularCoefficient_on_horodisc :
    ∃ Y : ℝ, GlobalGenerator.cuspHeight ≤ Y ∧
      ∀ z : TriangleRegularPoint, z.val ∈ horodisc Y →
        GlobalRegular.regularCoefficient z = coefficientGerm (cuspQ z.val) := by
  obtain ⟨Y, hY, h⟩ := scalarDeriv_div_generator_on_horodisc
  refine ⟨Y, hY, fun z hz => ?_⟩
  rw [regularCoefficient_eq_scalarDeriv_div_generator]
  exact h z.val hz

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspScalar
