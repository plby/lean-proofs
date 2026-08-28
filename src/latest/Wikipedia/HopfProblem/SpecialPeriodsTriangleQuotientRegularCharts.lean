import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientRegularChartsTopology

/-!
# The regular charts of the full triangle quotient

Each covering chart of the regular quotient is extended through its actual
open embedding into the full orbit space. Pulling one of these charts back
along the full orbit projection is locally biholomorphic everywhere on its
domain. These assertions do not assume any complex atlas on the full quotient.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem

section OpenSource

variable {E F H K M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K)

/-- A local biholomorphism on an open source is also locally biholomorphic
as an ambient map. This uses the inherited open-subset charts. -/
theorem isLocalDiffeomorphAt_of_comp_opensSubtypeVal
    (U : TopologicalSpace.Opens M) {f : M → N} (x : U)
    (hf : IsLocalDiffeomorphAt I J ω (f ∘ (Subtype.val : U → M)) x) :
    IsLocalDiffeomorphAt I J ω f (x : M) := by
  obtain ⟨φ, hx, he⟩ := hf
  let e := opensInclusionPartialDiffeomorph I U ⟨x⟩
  have hxU : (x : M) ∈ e.target := by
    change (x : M) ∈ (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).target
    rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    change (x : M) ∈ U
    exact x.property
  have hinv : e.symm (x : M) = x := e.left_inv (mem_univ x)
  refine ⟨e.symm.trans φ, ⟨hxU, ?_⟩, ?_⟩
  · change e.symm (x : M) ∈ φ.source
    rw [hinv]
    exact hx
  intro y hy
  have hval : ((e.symm y : U) : M) = y := e.right_inv hy.1
  change f y = φ (e.symm y)
  exact (congrArg f hval.symm).trans (he hy.2)

end OpenSource

namespace SpecialPeriods

attribute [local instance] triangleRegularQuotientChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleRegularQuotient :=
  triangleRegularQuotient_isManifold

/-- A genuine regular chart on the full orbit quotient. Only the already
constructed covering atlas on the regular quotient occurs in this definition. -/
def regularFullChart (x : TriangleRegularQuotient) :
    OpenPartialHomeomorph TriangleOrbitSpace ℂ :=
  triangleRegularOrbitParametrization.symm.trans (chartAt ℂ x)

theorem regularFullChart_mem_source_iff (x : TriangleRegularQuotient)
    (y : TriangleOrbitSpace) :
    y ∈ (regularFullChart x).source ↔
      y ∈ triangleOrbitRegularDomain ∧
        triangleRegularOrbitParametrization.symm y ∈ (chartAt ℂ x).source := by
  change (y ∈ triangleRegularOrbitParametrization.target ∧
    triangleRegularOrbitParametrization.symm y ∈ (chartAt ℂ x).source) ↔ _
  rw [triangleRegularOrbitParametrization_target]
  rfl

theorem regularFullChart_source_subset (x : TriangleRegularQuotient) :
    (regularFullChart x).source ⊆ triangleOrbitRegularDomain :=
  fun _ hy => ((regularFullChart_mem_source_iff x _).mp hy).1

@[simp] theorem regularFullChart_apply_inclusion (x y : TriangleRegularQuotient) :
    regularFullChart x (triangleRegularToOrbit y) = chartAt ℂ x y := by
  change chartAt ℂ x (triangleRegularOrbitParametrization.symm
    (triangleRegularToOrbit y)) = _
  rw [triangleRegularOrbitParametrization_symm_apply]

@[simp] theorem regularFullChart_mem_source_inclusion_iff
    (x y : TriangleRegularQuotient) :
    triangleRegularToOrbit y ∈ (regularFullChart x).source ↔
      y ∈ (chartAt ℂ x).source := by
  rw [regularFullChart_mem_source_iff, triangleRegularOrbitParametrization_symm_apply]
  exact and_iff_right ⟨y, rfl⟩

/-- The chart indexed by a regular quotient point contains that point's
image in the full orbit space. -/
theorem regularFullChart_mem_source (x : TriangleRegularQuotient) :
    triangleRegularToOrbit x ∈ (regularFullChart x).source :=
  (regularFullChart_mem_source_inclusion_iff x x).mpr (mem_chart_source ℂ x)

theorem exists_regularFullChart (y : TriangleOrbitSpace)
    (hy : y ∈ triangleOrbitRegularDomain) :
    ∃ x : TriangleRegularQuotient, y ∈ (regularFullChart x).source := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, regularFullChart_mem_source x⟩

theorem regularFullChart_iUnion_source :
    (⋃ x : TriangleRegularQuotient, (regularFullChart x).source) =
      (triangleOrbitRegularDomain : Set TriangleOrbitSpace) := by
  apply le_antisymm
  · exact iUnion_subset fun x => regularFullChart_source_subset x
  · intro y hy
    obtain ⟨x, hx⟩ := exists_regularFullChart y hy
    exact mem_iUnion.mpr ⟨x, hx⟩

/-- On a regular point, the pulled-back full chart is exactly the original
covering-quotient chart of its regular projection. -/
@[simp] theorem regularFullChart_projection (x : TriangleRegularQuotient)
    (z : TriangleRegularPoint) :
    regularFullChart x (triangleOrbitProjection z.val) =
      chartAt ℂ x (triangleRegularProject z) := by
  rw [← triangleRegularToOrbit_project z, regularFullChart_apply_inclusion]

/-- A coordinate chart of the regular quotient, with its established analytic
atlas, is an analytic partial diffeomorphism. -/
def triangleRegularCoordinatePartial (x : TriangleRegularQuotient) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleRegularQuotient ℂ ω where
  toPartialEquiv := (chartAt ℂ x).toPartialEquiv
  open_source := (chartAt ℂ x).open_source
  open_target := (chartAt ℂ x).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

/-- Every pullback of a regular full-quotient chart is locally biholomorphic
on its entire preimage in the original upper half-plane. -/
theorem regularFullChart_pullback_isLocalDiffeomorphAt
    (x : TriangleRegularQuotient) {z : ℍ}
    (hz : triangleOrbitProjection z ∈ (regularFullChart x).source) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      (regularFullChart x ∘ triangleOrbitProjection) z := by
  have hzreg : z ∈ triangleRegularLocus :=
    (triangleOrbitProjection_mem_regularDomain_iff z).mp
      (regularFullChart_source_subset x hz)
  let a : TriangleRegularPoint := ⟨z, hzreg⟩
  have hsource : triangleRegularProject a ∈ (chartAt ℂ x).source := by
    apply (regularFullChart_mem_source_inclusion_iff x (triangleRegularProject a)).mp
    simpa only [triangleRegularToOrbit_project] using hz
  have hchart : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x)
      (triangleRegularProject a) :=
    (triangleRegularCoordinatePartial x).isLocalDiffeomorphAt _ _ _ hsource
  have hreg : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      (chartAt ℂ x ∘ triangleRegularProject) a :=
    (triangleRegularProject_isLocalDiffeomorph a).comp (K := 𝓘(ℂ)) (P := ℂ) hchart
  have heq : (regularFullChart x ∘ triangleOrbitProjection) ∘
      (Subtype.val : TriangleRegularPoint → ℍ) = chartAt ℂ x ∘ triangleRegularProject := by
    funext w
    exact regularFullChart_projection x w
  have hrestricted : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      ((regularFullChart x ∘ triangleOrbitProjection) ∘
        (Subtype.val : TriangleRegularPoint → ℍ)) a := by
    rw [heq]
    exact hreg
  exact isLocalDiffeomorphAt_of_comp_opensSubtypeVal 𝓘(ℂ) 𝓘(ℂ)
    triangleRegularDomain a hrestricted

/-- Holomorphicity of every regular chart pullback, before constructing the
complex atlas on the full quotient. -/
theorem regularFullChart_pullback_holomorphic (x : TriangleRegularQuotient) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (regularFullChart x ∘ triangleOrbitProjection)
      (triangleOrbitProjection ⁻¹' (regularFullChart x).source) :=
  fun _ hz => (regularFullChart_pullback_isLocalDiffeomorphAt x hz).contMDiffAt.contMDiffWithinAt

end SpecialPeriods

end Wikipedia.HopfProblem
