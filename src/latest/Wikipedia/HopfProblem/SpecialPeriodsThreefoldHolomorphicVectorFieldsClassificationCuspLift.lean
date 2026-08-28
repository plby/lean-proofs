import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationLift
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspChart
import Wikipedia.HopfProblem.CuspPuncturedManifold

/-!
# Native vector-field coefficients at the filled cusp

The actual reference toric chart maps locally biholomorphically through
the original tube quotient into the glued threefold. Pulling back a
holomorphic tangent section therefore gives holomorphic native vector
coefficients, including along the transverse disc through the filled cusp.
-/

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

open ToricCharts

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace
  Threefold.space_isManifold

private theorem referenceToricInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph I₃ I₃ ω
      (ToricSpace.inclusion ToricSpace.referenceTriangle) := by
  have he : (ToricSpace.parametrization ToricSpace.referenceTriangle).symm ∈
      IsManifold.maximalAtlas I₃ ω ToricSpace.Space :=
    IsManifold.subset_maximalAtlas (mem_range_self ToricSpace.referenceTriangle)
  intro w
  refine ⟨{
    toPartialEquiv := (ToricSpace.parametrization ToricSpace.referenceTriangle).toPartialEquiv
    open_source := (ToricSpace.parametrization ToricSpace.referenceTriangle).open_source
    open_target := (ToricSpace.parametrization ToricSpace.referenceTriangle).open_target
    contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas he
    contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas he }, mem_univ w, ?_⟩
  intro y _
  rfl

private theorem referenceToricLift_isLocalDiffeomorph :
    IsLocalDiffeomorph I₃ I₃ ω HolomorphicForms.Cusp.referenceLift :=
  isLocalDiffeomorph_restrictOpens I₃ I₃ referenceToricInclusion_isLocalDiffeomorph
    HolomorphicForms.Cusp.referenceDomain
    (ToricSpace.tubeOpen (CuspQuotient.disc CuspGeometry.data.radius))
    (fun w hw => (HolomorphicForms.Cusp.referenceLift ⟨w, hw⟩).property)

/-- The genuine reference chart remains locally biholomorphic through the
original toric tube quotient and the native cusp inclusion. -/
theorem cuspReferenceMap_isLocalDiffeomorph :
    IsLocalDiffeomorph I₃ IF ω HolomorphicForms.Cusp.referenceMap := by
  let := CuspQuotient.chartedSpace CuspGeometry.data.correction CuspGeometry.data.radius
    CuspGeometry.data.radius_pos CuspGeometry.data.radius_lt_one
    CuspGeometry.data.holomorphic CuspGeometry.data.smallDrift
  let : ChartedSpace (CoordinateSpace 3) CuspGeometry.LocalSpace := CuspGeometry.nativeChartedSpace
  intro w
  have hq : IsLocalDiffeomorphAt I₃ I₃ ω
      (CuspQuotient.quotientMap CuspGeometry.data.correction CuspGeometry.data.radius :
        ToricSpace.Tube (CuspQuotient.disc CuspGeometry.data.radius) → CuspGeometry.LocalSpace)
      (HolomorphicForms.Cusp.referenceLift w) :=
    CuspUniformization.quotientMap_isLocalDiffeomorph
      CuspGeometry.data.correction CuspGeometry.data.radius CuspGeometry.data.radius_pos
      CuspGeometry.data.radius_lt_one CuspGeometry.data.holomorphic CuspGeometry.data.smallDrift
      (HolomorphicForms.Cusp.referenceLift w)
  have hr : IsLocalDiffeomorphAt I₃ I₃ ω HolomorphicForms.Cusp.referenceQuotient w :=
    (referenceToricLift_isLocalDiffeomorph w).comp (K := I₃) (P := CuspGeometry.LocalSpace) hq
  exact hr.comp (K := IF) (P := Threefold.Space)
    (CuspGeometry.inclusion_isLocalDiffeomorph (HolomorphicForms.Cusp.referenceQuotient w))

/-- The lifted native tangent field in the actual filled reference chart. -/
noncomputable def cuspReferenceLift (v : Threefold.HolomorphicVectorFields.Field) :
    Wikipedia.HopfProblem.HolomorphicVectorFields.Field
      (CoordinateSpace 3) HolomorphicForms.Cusp.referenceDomain :=
  pullback HolomorphicForms.Cusp.referenceMap cuspReferenceMap_isLocalDiffeomorph v

/-- The actual cusp reference-map derivative sends the lift to the original field. -/
theorem cuspReferenceLift_map (v : Threefold.HolomorphicVectorFields.Field)
    (w : HolomorphicForms.Cusp.referenceDomain) :
    mfderiv I₃ IF HolomorphicForms.Cusp.referenceMap w (cuspReferenceLift v w) =
      v (HolomorphicForms.Cusp.referenceMap w) :=
  pullback_map HolomorphicForms.Cusp.referenceMap cuspReferenceMap_isLocalDiffeomorph v w

/-- The literal three native tangent coordinates, without changing the reference atlas. -/
noncomputable def cuspReferenceCoefficients (v : Threefold.HolomorphicVectorFields.Field)
    (w : HolomorphicForms.Cusp.referenceDomain) : CoordinateSpace 3 :=
  cuspReferenceLift v w

theorem cuspReferenceCoefficients_holomorphic (v : Threefold.HolomorphicVectorFields.Field) :
    ContMDiff I₃ I₃ ω (cuspReferenceCoefficients v) :=
  nativeValue_holomorphic_of_constant_charts
    (CoordinateSpace 3) HolomorphicForms.Cusp.referenceDomain
    HolomorphicForms.Cusp.reference_chart_eq (cuspReferenceLift v)

/-- The two logarithmically normalized vertical coefficients along the
entire filled axis with first coordinate equal to the cusp parameter. -/
noncomputable def cuspAxisCoefficient (v : Threefold.HolomorphicVectorFields.Field)
    (i : Fin 2) (q : CuspQuotient.disc CuspGeometry.data.radius) : ℂ :=
  cuspReferenceCoefficients v (HolomorphicForms.Cusp.axisInclusion 0 q) i.succ /
    (2 * (Real.pi : ℂ) * Complex.I)

theorem cuspAxisCoefficient_holomorphic (v : Threefold.HolomorphicVectorFields.Field)
    (i : Fin 2) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspAxisCoefficient v i) := by
  have hc : ContMDiff I₃ 𝓘(ℂ) ω
      (fun w => cuspReferenceCoefficients v w i.succ) :=
    (contDiff_apply ℂ ℂ i.succ).contMDiff.comp (cuspReferenceCoefficients_holomorphic v)
  have ha := hc.comp (HolomorphicForms.Cusp.axisInclusion_holomorphic 0)
  change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
    (fun q => cuspReferenceCoefficients v (HolomorphicForms.Cusp.axisInclusion 0 q) i.succ /
      (2 * (Real.pi : ℂ) * Complex.I))
  simp only [div_eq_mul_inv]
  exact ha.mul (contMDiff_const (c := (2 * (Real.pi : ℂ) * Complex.I)⁻¹))

/-- A concrete ambient representative of the native coefficient germ, zero
outside the original open cusp disc. -/
noncomputable def cuspGerm (v : Threefold.HolomorphicVectorFields.Field)
    (i : Fin 2) (q : ℂ) : ℂ := by
  classical
  exact if hq : q ∈ CuspQuotient.disc CuspGeometry.data.radius then
    cuspAxisCoefficient v i ⟨q, hq⟩ else 0

theorem cuspGerm_of_mem (v : Threefold.HolomorphicVectorFields.Field)
    (i : Fin 2) {q : ℂ} (hq : q ∈ CuspQuotient.disc CuspGeometry.data.radius) :
    cuspGerm v i q = cuspAxisCoefficient v i ⟨q, hq⟩ := by
  simp only [cuspGerm, dif_pos hq]

/-- The ambient representative is analytic at every point of the original cusp disc. -/
theorem cuspGerm_analyticAt (v : Threefold.HolomorphicVectorFields.Field)
    (i : Fin 2) {q : ℂ} (hq : q ∈ CuspQuotient.disc CuspGeometry.data.radius) :
    AnalyticAt ℂ (cuspGerm v i) q := by
  have he : (fun z : CuspQuotient.disc CuspGeometry.data.radius => cuspGerm v i z) =
      cuspAxisCoefficient v i := funext fun z => cuspGerm_of_mem v i z.property
  have hs : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : CuspQuotient.disc CuspGeometry.data.radius => cuspGerm v i z) ⟨q, hq⟩ := by
    rw [he]
    exact cuspAxisCoefficient_holomorphic v i ⟨q, hq⟩
  have ha : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspGerm v i) q :=
    contMDiffAt_subtype_iff.mp hs
  exact ha.contDiffAt.analyticAt

/-- In particular the normalized native coefficient is analytic at the filled cusp. -/
theorem cuspGerm_analyticAt_zero (v : Threefold.HolomorphicVectorFields.Field) (i : Fin 2) :
    AnalyticAt ℂ (cuspGerm v i) 0 :=
  cuspGerm_analyticAt v i (by
    simpa [CuspQuotient.disc] using CuspGeometry.data.radius_pos)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
