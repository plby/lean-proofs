import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultLocalChart
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultLifts

/-!
# Descent of smooth plane germs through original torus charts

A smooth function on the native cover defines a genuine local torus
section. Any condition holding near the preferred lift can be retained
on the smaller open set, together with equality of the actual lifted
section germ and the original plane germ at every point of that set.
-/

noncomputable section

open Set TopologicalSpace Filter Metric
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

/-- Evaluating the actual lift in an original valid chart recovers the
given original section value. -/
theorem liftSection_chart_apply (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) (x y : p.Torus)
    (hy : y ∈ chartSource p x) (hyU : y ∈ U) :
    liftSection p U s (DiscreteQuotient.chart p.lattice x y) = s ⟨y, hyU⟩ := by
  change smoothExtend p U s
    (p.lattice.mkQ (DiscreteQuotient.chart p.lattice x y)) = _
  rw [DiscreteQuotient.mkQ_chart p.lattice x y hy]
  exact smoothExtend_apply p U s y hyU

/-- Descend a genuine smooth native plane germ on a smaller original
torus open, retaining any prescribed condition on its chart coordinates. -/
theorem exists_local_chart_section (p : PeriodDomain) (U : Opens p.Torus)
    (x : p.Torus) (hx : x ∈ U) (u : ComplexPlane₂ → ℂ) (hu : ContDiff ℝ ∞ u)
    {P : ComplexPlane₂ → Prop}
    (hP : ∀ᶠ z in 𝓝 (DiscreteQuotient.chart p.lattice x x), P z) :
    ∃ (V : Opens p.Torus) (_hVU : V ≤ U), x ∈ V ∧ V ≤ chartSource p x ∧
      ∃ t : SmoothSection p V, ∀ y : V,
        P (DiscreteQuotient.chart p.lattice x (y : p.Torus)) ∧
          liftSection p V t =ᶠ[𝓝 (DiscreteQuotient.chart p.lattice x (y : p.Torus))] u := by
  have hz : DiscreteQuotient.chart p.lattice x x ∈ coverOpen p U := by
    change p.lattice.mkQ (DiscreteQuotient.chart p.lattice x x) ∈ U
    rw [DiscreteQuotient.mkQ_chart p.lattice x x (mem_chartSource p x)]
    exact hx
  have hnear : ∀ᶠ z in 𝓝 (DiscreteQuotient.chart p.lattice x x),
      z ∈ coverOpen p U ∧ P z :=
    Filter.Eventually.and ((coverOpen p U).isOpen.mem_nhds hz) hP
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let W : Opens ComplexPlane₂ :=
    ⟨ball (DiscreteQuotient.chart p.lattice x x) r, isOpen_ball⟩
  let V := chartImage p x W
  have hVU : V ≤ U := chartImage_le p x W U (fun _ hw => (hball hw).1)
  have hVS : V ≤ chartSource p x := chartImage_le_source p x W
  refine ⟨V, hVU, mem_chartImage_center p x W (mem_ball_self hr), hVS,
    chartSection p x V hVS u hu, ?_⟩
  intro y
  have hys : (y : p.Torus) ∈ chartSource p x := hVS y.property
  have hyV : p.lattice.mkQ (DiscreteQuotient.chart p.lattice x (y : p.Torus)) ∈ V := by
    rw [DiscreteQuotient.mkQ_chart p.lattice x (y : p.Torus) hys]
    exact y.property
  exact ⟨(hball (chartImage_chart_mem p x W y.property)).2,
    chartSection_lift_germ p x V hVS u hu
      ((DiscreteQuotient.chart p.lattice x).map_source hys) hyV⟩

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
