import Wikipedia.HopfProblem.CoveringManifold

/-!
# Complex manifolds from free finite holomorphic actions

This is the actual orbit quotient, endowed with its quotient topology.
Finiteness gives proper discontinuity, and freeness makes the projection
a covering map.  The complex atlas is constructed from its local lifts.
The selected structures below are not global instances, so different
quotient presentations cannot silently install competing atlases.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.FiniteQuotient

variable (G M : Type*) [Group G] [MulAction G M]

/-- The actual quotient by the finite-group orbits. -/
abbrev Space := MulAction.orbitRel.Quotient G M

/-- The orbit-quotient projection. -/
def project : M → Space G M := Quotient.mk (MulAction.orbitRel G M)

theorem project_surjective : Function.Surjective (project G M) := Quotient.mk_surjective

theorem project_eq_iff_mem_orbit (x y : M) :
    project G M x = project G M y ↔ x ∈ MulAction.orbit G y := Quotient.eq''

@[simp] theorem project_smul (g : G) (x : M) :
    project G M (g • x) = project G M x :=
  (project_eq_iff_mem_orbit G M _ _).mpr ⟨g, rfl⟩

section Topology

variable [TopologicalSpace M]

theorem project_isQuotientMap : IsQuotientMap (project G M) :=
  isQuotientMap_quotient_mk'

theorem project_continuous : Continuous (project G M) :=
  (project_isQuotientMap G M).continuous

theorem project_isOpenQuotientMap [ContinuousConstSMul G M] :
    IsOpenQuotientMap (project G M) := MulAction.isOpenQuotientMap_quotientMk

theorem properlyDiscontinuous [Finite G] : ProperlyDiscontinuousSMul G M := inferInstance

theorem spaceCompactSpace [CompactSpace M] : CompactSpace (Space G M) := inferInstance

theorem spaceSecondCountableTopology [SecondCountableTopology M] [ContinuousConstSMul G M] :
    SecondCountableTopology (Space G M) :=
  (project_isQuotientMap G M).secondCountableTopology
    (project_isOpenQuotientMap G M).isOpenMap

theorem spaceLocallyCompactSpace [LocallyCompactSpace M] [ContinuousConstSMul G M] :
    LocallyCompactSpace (Space G M) :=
  (project_isOpenQuotientMap G M).locallyCompactSpace

theorem spaceT2Space [Finite G] [LocallyCompactSpace M] [T2Space M]
    [ContinuousConstSMul G M] : T2Space (Space G M) := inferInstance

variable [Finite G] [LocallyCompactSpace M] [T2Space M]
    [ContinuousConstSMul G M] [IsCancelSMul G M]

/-- A free finite action gives a genuine quotient covering map. -/
theorem project_isQuotientCoveringMap : IsQuotientCoveringMap (project G M) G :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem project_isCoveringMap : IsCoveringMap (project G M) :=
  (project_isQuotientCoveringMap G M).isCoveringMap

theorem project_isLocalHomeomorph : IsLocalHomeomorph (project G M) :=
  (project_isCoveringMap G M).isLocalHomeomorph

/-- A local inverse around a chosen point of the covering manifold. -/
def localInverse (x : M) : OpenPartialHomeomorph (Space G M) M :=
  CoveringQuotient.localInverse (project_isQuotientCoveringMap G M) x

@[simp] theorem localInverse_symm (x : M) :
    (localInverse G M x).symm = project G M :=
  CoveringQuotient.localInverse_symm (project_isQuotientCoveringMap G M) x

theorem project_localInverse (x : M) {y : Space G M}
    (hy : y ∈ (localInverse G M x).source) :
    project G M (localInverse G M x y) = y :=
  CoveringQuotient.project_localInverse (project_isQuotientCoveringMap G M) x hy

/-- Each fibre of a free orbit quotient is a torsor for the acting group. -/
def fibreEquivGroup (x : Space G M) : (project G M ⁻¹' {x}) ≃ G :=
  (project_isQuotientCoveringMap G M).fiberEquivGroup
    ⟨(project_surjective G M x).choose, (project_surjective G M x).choose_spec⟩

/-- The covering degree is the order of the finite group. -/
theorem fibre_card (x : Space G M) : Nat.card (project G M ⁻¹' {x}) = Nat.card G :=
  Nat.card_congr (fibreEquivGroup G M x)

theorem fibre_finite (x : Space G M) : (project G M ⁻¹' {x}).Finite := by
  let := Finite.of_equiv G (fibreEquivGroup G M x).symm
  exact Set.toFinite _

end Topology

section ComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M]

/-- The continuity needed by the quotient construction follows from the
proved holomorphicity of the finite action. -/
theorem continuousConstSMul_of_holomorphic
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) ω (fun x : M => g • x)) : ContinuousConstSMul G M where
  continuous_const_smul g := (hG g).continuous

variable [Finite G] [LocallyCompactSpace M] [T2Space M]
    [ContinuousConstSMul G M] [IsCancelSMul G M]

/-- The selected complex charts on the actual finite orbit quotient. -/
@[instance_reducible] def chartedSpace : ChartedSpace E (Space G M) :=
  CoveringQuotient.chartedSpace (E := E) (project_isQuotientCoveringMap G M)

variable [IsManifold (modelWithCornersSelf ℂ E) ω M]
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) ω (fun x : M => g • x))

include hG

/-- Holomorphic deck transformations give compatible complex quotient charts. -/
theorem isManifold :
    letI := chartedSpace (E := E) G M
    IsManifold (modelWithCornersSelf ℂ E) ω (Space G M) :=
  CoveringQuotient.isManifold (project_isQuotientCoveringMap G M) ω hG

/-- The projection is holomorphic for the constructed quotient atlas. -/
theorem project_holomorphic :
    letI := chartedSpace (E := E) G M
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (project G M) :=
  CoveringQuotient.contMDiff_project (project_isQuotientCoveringMap G M) ω hG

/-- Every chosen local inverse of the quotient projection is holomorphic. -/
theorem localInverse_holomorphic (x : M) :
    letI := chartedSpace (E := E) G M
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (localInverse G M x) (localInverse G M x).source :=
  CoveringQuotient.localInverse_holomorphic (project_isQuotientCoveringMap G M) ω hG x

end ComplexStructure

end Wikipedia.HopfProblem.Elliptic.FiniteQuotient
