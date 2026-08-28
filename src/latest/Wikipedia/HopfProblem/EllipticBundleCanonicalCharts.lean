import Wikipedia.HopfProblem.EllipticBundleCanonicalAffine
import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedCore
import Wikipedia.HopfProblem.CoveringVolumeCoordinates

/-!
# Derivatives of the actual elliptic surface charts

The chart changes of the quotient surface agree locally with one of the
actual affine deck transformations. Its deck element is precisely the
element used by the independently constructed character transition data.
Thus the following derivative formula relates the surface atlas to that
cocycle, without replacing either atlas or declaring a character bundle
to be the canonical bundle by definition.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.Elliptic.CanonicalBundle

open HolomorphicCharacterBundle

section QuotientCoordinates

variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q]
    [Group G] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G)

omit [NormedSpace ℂ E] in
theorem quotient_chart_source_subset (i : Q) :
    (CoveringQuotient.chart (E := E) hq i).source ⊆ AssociatedCore.baseSet hq i :=
  fun _ hx => hx.1

omit [NormedSpace ℂ E] in
theorem quotient_chart_inner_inverse (i : Q) {x : Q}
    (hx : x ∈ (CoveringQuotient.chart (E := E) hq i).source) :
    (chartAt E (CoveringQuotient.representative hq i)).symm
      (CoveringQuotient.chart (E := E) hq i x) = AssociatedCore.lift hq i x :=
  (chartAt E (CoveringQuotient.representative hq i)).left_inv hx.2

omit [NormedSpace ℂ E] in
/-- The local deck transformation in an actual quotient chart transition
is the same one used in the character cocycle. -/
theorem quotient_transition_eventually_deck_at (i k x : Q)
    (hi : x ∈ (CoveringQuotient.chart (E := E) hq i).source)
    (hk : x ∈ (CoveringQuotient.chart (E := E) hq k).source) :
    (((CoveringQuotient.chart (E := E) hq i).symm.trans
      (CoveringQuotient.chart (E := E) hq k)) : E → E) =ᶠ[
        𝓝 (CoveringQuotient.chart (E := E) hq i x)]
      (chartAt E (CoveringQuotient.representative hq k) ∘
        (fun a : M => AssociatedCore.deck hq i k x • a) ∘
          (chartAt E (CoveringQuotient.representative hq i)).symm) := by
  have hp : q (AssociatedCore.lift hq i x) = x := AssociatedCore.lift_project hq i hi.1
  have hsrc : q (AssociatedCore.lift hq i x) ∈
      (CoveringQuotient.localInverse hq (CoveringQuotient.representative hq k)).source := by
    rw [hp]
    exact hk.1
  obtain ⟨g, hg, he⟩ := CoveringQuotient.localInverse_eventually_deck hq
    hq.continuous_const_smul (CoveringQuotient.representative hq k)
      (AssociatedCore.lift hq i x) hsrc
  rw [hp] at hg
  have hd : AssociatedCore.deck hq i k x = g :=
    AssociatedCore.deck_eq_of_smul hq i k ⟨hi.1, hk.1⟩ g hg.symm
  rw [← hd] at he
  have hz : CoveringQuotient.chart (E := E) hq i x ∈
      (chartAt E (CoveringQuotient.representative hq i)).target :=
    (chartAt E (CoveringQuotient.representative hq i)).map_source hi.2
  have ht : Filter.Tendsto (chartAt E (CoveringQuotient.representative hq i)).symm
      (𝓝 (CoveringQuotient.chart (E := E) hq i x)) (𝓝 (AssociatedCore.lift hq i x)) := by
    simpa only [ContinuousAt, quotient_chart_inner_inverse hq i hi] using
      (chartAt E (CoveringQuotient.representative hq i)).symm.continuousAt hz
  rw [CoveringQuotient.transition_eq]
  exact (he.comp_tendsto ht).fun_comp (chartAt E (CoveringQuotient.representative hq k))

end QuotientCoordinates

/-- The actual free finite affine action gives the surface quotient
covering, with the original quotient projection. -/
theorem surfaceCovering (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := affineAction j p v hv.1
    IsQuotientCoveringMap (surfaceProjection j p v hv) (CyclicGroup j) := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  exact FiniteQuotient.project_isQuotientCoveringMap (CyclicGroup j) p.val.Torus

/-- On every genuine surface-chart overlap, the chart derivative is the
power of the linear monodromy selected by the actual character deck cocycle. -/
theorem surface_chart_hasFDerivAt (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (i k x : Surface j p v hv)
    (hi : x ∈ (chartAt ComplexPlane₂ i).source)
    (hk : x ∈ (chartAt ComplexPlane₂ k).source) :
    letI := affineAction j p v hv.1
    HasFDerivAt ((chartAt ComplexPlane₂ i).symm.trans (chartAt ComplexPlane₂ k))
      ((linearEquiv j p).toContinuousLinearMap ^
        (AssociatedCore.deck (surfaceCovering j p v hv) i k x).toAdd.val)
      (chartAt ComplexPlane₂ i x) := by
  let := affineAction j p v hv.1
  let hq := surfaceCovering j p v hv
  change x ∈ (CoveringQuotient.chart (E := ComplexPlane₂) hq i).source at hi
  change x ∈ (CoveringQuotient.chart (E := ComplexPlane₂) hq k).source at hk
  let g := AssociatedCore.deck hq i k x
  have htarget : g • (chartAt ComplexPlane₂ (CoveringQuotient.representative hq i)).symm
      (CoveringQuotient.chart (E := ComplexPlane₂) hq i x) ∈
        (chartAt ComplexPlane₂ (CoveringQuotient.representative hq k)).source := by
    rw [quotient_chart_inner_inverse hq i hi]
    change AssociatedCore.deck hq i k x • AssociatedCore.lift hq i x ∈ _
    rw [AssociatedCore.deck_spec hq i k ⟨hi.1, hk.1⟩]
    exact hk.2
  have hder := affineAction_chart_hasFDerivAt j p v hv.1 g
    (CoveringQuotient.representative hq i) (CoveringQuotient.representative hq k)
    (CoveringQuotient.chart (E := ComplexPlane₂) hq i x) htarget
  exact hder.congr_of_eventuallyEq (quotient_transition_eventually_deck_at hq i k x hi hk)

theorem surface_chart_det_fderiv (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (i k x : Surface j p v hv)
    (hi : x ∈ (chartAt ComplexPlane₂ i).source)
    (hk : x ∈ (chartAt ComplexPlane₂ k).source) :
    letI := affineAction j p v hv.1
    LinearMap.det (fderiv ℂ
      ((chartAt ComplexPlane₂ i).symm.trans (chartAt ComplexPlane₂ k))
      (chartAt ComplexPlane₂ i x)).toLinearMap =
        (LinearMap.det (linearEquiv j p).toLinearMap) ^
          (AssociatedCore.deck (surfaceCovering j p v hv) i k x).toAdd.val := by
  let := affineAction j p v hv.1
  rw [(surface_chart_hasFDerivAt j p v hv i k x hi hk).fderiv,
    ContinuousLinearMap.toLinearMap_pow, map_pow]
  rfl

/-- The same derivative identity on the entire coordinate overlap, with
the represented surface point determined by the inverse source chart. -/
theorem surface_chart_det_fderiv_on_overlap (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (i k : Surface j p v hv) {z : ComplexPlane₂}
    (hz : z ∈ ((chartAt ComplexPlane₂ i).symm.trans (chartAt ComplexPlane₂ k)).source) :
    letI := affineAction j p v hv.1
    LinearMap.det (fderiv ℂ
      ((chartAt ComplexPlane₂ i).symm.trans (chartAt ComplexPlane₂ k)) z).toLinearMap =
        (LinearMap.det (linearEquiv j p).toLinearMap) ^
          (AssociatedCore.deck (surfaceCovering j p v hv) i k
            ((chartAt ComplexPlane₂ i).symm z)).toAdd.val := by
  let := affineAction j p v hv.1
  simpa only [(chartAt ComplexPlane₂ i).right_inv hz.1] using
    surface_chart_det_fderiv j p v hv i k ((chartAt ComplexPlane₂ i).symm z)
      ((chartAt ComplexPlane₂ i).map_target hz.1) hz.2

end Wikipedia.HopfProblem.Elliptic.CanonicalBundle
