import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultSections
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultLocalCoordinates
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultLocalTransfer

/-!
# Actual local exactness of the native period-torus Dolbeault sequence

The native coordinate germ solvers are descended through an original
quotient chart to genuine smooth sections on smaller torus opens. Their
derivatives are checked using the literal quotient lifts and equality of
germs. No primitive is assumed to descend globally, and no closedness or
smoothness outside the original section domain is imposed.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

open PeriodTorusLineBundleClassification
open PeriodTorusLineBundleClassificationHolomorphicFrame

/-- A native derivative can be computed from any equal lifted germ in
an original valid quotient chart. -/
theorem derivativeSection_eq_of_chart_germ (p : PeriodDomain) (i : Fin 2)
    (V : Opens p.Torus) (x : p.Torus) (hV : V ≤ chartSource p x)
    (t : SmoothSection p V) (u : ComplexPlane₂ → ℂ) (y : V)
    (he : liftSection p V t =ᶠ[𝓝 (DiscreteQuotient.chart p.lattice x (y : p.Torus))] u) :
    derivativeSection p i V t y =
      dbarCoordinate u i (DiscreteQuotient.chart p.lattice x (y : p.Torus)) := by
  have hy : p.lattice.mkQ (DiscreteQuotient.chart p.lattice x (y : p.Torus)) = y :=
    DiscreteQuotient.mkQ_chart p.lattice x y (hV y.property)
  have hyV : p.lattice.mkQ (DiscreteQuotient.chart p.lattice x (y : p.Torus)) ∈ V := by
    rw [hy]
    exact y.property
  have hpoint : (⟨p.lattice.mkQ (DiscreteQuotient.chart p.lattice x (y : p.Torus)),
      hyV⟩ : V) = y := Subtype.ext hy
  have hder := derivativeSection_pullback p i V t
    (DiscreteQuotient.chart p.lattice x (y : p.Torus)) hyV
  rw [hpoint] at hder
  exact hder.trans (dbarCoordinate_congr he i)

/-- Vanishing of the actual top differential gives the genuine mixed
coordinate closedness equation throughout the lifted original domain. -/
theorem closed_lift_of_topSection_zero (p : PeriodDomain) (U : Opens p.Torus)
    (s : PairSection p U) (hs : topSection p U s = 0) :
    ∀ z ∈ coverOpen p U,
      dbarCoordinate (liftSection p U s.2) 0 z =
        dbarCoordinate (liftSection p U s.1) 1 z := by
  intro z hz
  have h := congrArg (fun t : SmoothSection p U => t ⟨p.lattice.mkQ z, hz⟩) hs
  rw [topSection_pullback p U s z hz] at h
  exact sub_eq_zero.mp h

/-- Every actual closed smooth pair has a primitive section on an
original smaller torus open containing the given point. -/
theorem exists_local_primitive (p : PeriodDomain) (U : Opens p.Torus)
    (x : p.Torus) (hx : x ∈ U) (s : PairSection p U) (hs : topSection p U s = 0) :
    ∃ (V : Opens p.Torus) (hVU : V ≤ U), x ∈ V ∧
      ∃ t : SmoothSection p V, differentialSection p V t = pairRestriction p hVU s := by
  have hz : DiscreteQuotient.chart p.lattice x x ∈ coverOpen p U := by
    change p.lattice.mkQ (DiscreteQuotient.chart p.lattice x x) ∈ U
    rw [DiscreteQuotient.mkQ_chart p.lattice x x (mem_chartSource p x)]
    exact hx
  obtain ⟨u, hu, hfirst, hsecond⟩ := exists_native_closed_primitive_germ
    (coverOpen p U).isOpen (liftSection_contDiffOn p U s.1)
    (liftSection_contDiffOn p U s.2) (closed_lift_of_topSection_zero p U s hs) hz
  obtain ⟨V, hVU, hxV, hVS, t, ht⟩ :=
    exists_local_chart_section p U x hx u hu (hfirst.and hsecond)
  refine ⟨V, hVU, hxV, t, ?_⟩
  apply Prod.ext
  · apply ContMDiffMap.ext
    intro y
    change derivativeSection p 0 V t y = s.1 ⟨(y : p.Torus), hVU y.property⟩
    exact (derivativeSection_eq_of_chart_germ p 0 V x hVS t u y (ht y).2).trans
      ((ht y).1.1.trans
        (liftSection_chart_apply p U s.1 x y (hVS y.property) (hVU y.property)))
  · apply ContMDiffMap.ext
    intro y
    change derivativeSection p 1 V t y = s.2 ⟨(y : p.Torus), hVU y.property⟩
    exact (derivativeSection_eq_of_chart_germ p 1 V x hVS t u y (ht y).2).trans
      ((ht y).1.2.trans
        (liftSection_chart_apply p U s.2 x y (hVS y.property) (hVU y.property)))

/-- Every actual smooth top coefficient has a primitive pair on an
original smaller torus open, with no closedness assumption. -/
theorem exists_local_top_primitive (p : PeriodDomain) (U : Opens p.Torus)
    (x : p.Torus) (hx : x ∈ U) (s : SmoothSection p U) :
    ∃ (V : Opens p.Torus) (hVU : V ≤ U), x ∈ V ∧
      ∃ t : PairSection p V, topSection p V t = restriction p hVU s := by
  have hz : DiscreteQuotient.chart p.lattice x x ∈ coverOpen p U := by
    change p.lattice.mkQ (DiscreteQuotient.chart p.lattice x x) ∈ U
    rw [DiscreteQuotient.mkQ_chart p.lattice x x (mem_chartSource p x)]
    exact hx
  obtain ⟨u, hu, hsecond⟩ := exists_native_second_primitive_germ
    (coverOpen p U).isOpen (liftSection_contDiffOn p U s) hz
  obtain ⟨V, hVU, hxV, hVS, t, ht⟩ :=
    exists_local_chart_section p U x hx u hu hsecond
  have hd : derivativeSection p 1 V t = restriction p hVU s := by
    apply ContMDiffMap.ext
    intro y
    change derivativeSection p 1 V t y = s ⟨(y : p.Torus), hVU y.property⟩
    exact (derivativeSection_eq_of_chart_germ p 1 V x hVS t u y (ht y).2).trans
      ((ht y).1.trans
        (liftSection_chart_apply p U s x y (hVS y.property) (hVU y.property)))
  refine ⟨V, hVU, hxV, (-t, 0), ?_⟩
  change derivativeSection p 0 V 0 - derivativeSection p 1 V (-t) = restriction p hVU s
  rw [map_zero, map_neg, zero_sub, neg_neg, hd]

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
