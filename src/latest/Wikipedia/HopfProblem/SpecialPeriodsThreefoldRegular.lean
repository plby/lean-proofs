import Wikipedia.HopfProblem.SpecialPeriodsTriangleCompactifiedOrdersCenters
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientLocalBiholomorph

/-!
# The actual regular patch of the compact triangle quotient

The regular base is the literal complement of the cusp and the two elliptic
orbit centers in the constructed compact curve.  Its inclusion from the
already constructed regular triangle quotient is the composition of the
actual quotient inclusion and the one-point-compactification inclusion.

The existing quotient atlases make this map locally biholomorphic.  Its
exact image is the three-puncture complement, so it gives a biholomorphism
onto that open patch with its inherited compact-curve atlas.  No sphere
uniformization or newly supplied charts are used.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] triangleRegularQuotientChartedSpace triangleOrbitChartedSpace
  triangleCompactifiedChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleRegularQuotient :=
  triangleRegularQuotient_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold
local instance : IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactified_isManifold

/-- The actual compact base with its cusp and two elliptic points removed. -/
def regularPatch : TopologicalSpace.Opens TriangleCompactifiedOrbitSpace :=
  ⟨({triangleCuspPoint, triangleCompactifiedCenterOne, triangleCompactifiedCenterTwo} :
      Set TriangleCompactifiedOrbitSpace)ᶜ,
    (((finite_singleton triangleCompactifiedCenterTwo).insert
      triangleCompactifiedCenterOne).insert triangleCuspPoint).isClosed.isOpen_compl⟩

@[simp] theorem mem_regularPatch (x : TriangleCompactifiedOrbitSpace) :
    x ∈ regularPatch ↔ x ≠ triangleCuspPoint ∧
      x ≠ triangleCompactifiedCenterOne ∧ x ≠ triangleCompactifiedCenterTwo := by
  simp only [regularPatch, TopologicalSpace.Opens.mem_mk, mem_compl_iff,
    mem_insert_iff, mem_singleton_iff, not_or]

/-- On the original orbit space, deleting the three compactified points
is exactly deleting the two elliptic orbit centers. -/
theorem openInclusion_mem_regularPatch_iff (q : TriangleOrbitSpace) :
    triangleOpenInclusion q ∈ regularPatch ↔ q ∈ triangleOrbitRegularDomain := by
  rw [mem_regularPatch, triangleOrbitRegularDomain_mem_iff]
  constructor
  · rintro ⟨_, h₁, h₂⟩
    exact ⟨fun h => h₁ (congrArg triangleOpenInclusion h),
      fun h => h₂ (congrArg triangleOpenInclusion h)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨triangleOpenInclusion_ne_cusp q,
      fun h => h₁ (OnePoint.coe_injective h), fun h => h₂ (OnePoint.coe_injective h)⟩

/-- The inverse image under the literal compactified projection is the
actual free-action locus in the upper half-plane. -/
theorem compactifiedProjection_mem_regularPatch_iff (z : ℍ) :
    triangleCompactifiedProjection z ∈ regularPatch ↔ z ∈ triangleRegularLocus := by
  change triangleOpenInclusion (triangleOrbitProjection z) ∈ regularPatch ↔ _
  rw [openInclusion_mem_regularPatch_iff, triangleOrbitProjection_mem_regularDomain_iff]

theorem compactifiedProjection_preimage_regularPatch :
    triangleCompactifiedProjection ⁻¹' (regularPatch : Set TriangleCompactifiedOrbitSpace) =
      triangleRegularLocus := Set.ext compactifiedProjection_mem_regularPatch_iff

/-- The genuine inclusion of regular orbits in the compactified quotient. -/
def regularInclusion : TriangleRegularQuotient → TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion ∘ triangleRegularToOrbit

@[simp] theorem regularInclusion_project (z : TriangleRegularPoint) :
    regularInclusion (triangleRegularProject z) = triangleCompactifiedProjection z.val := rfl

theorem regularInclusion_isOpenEmbedding : IsOpenEmbedding regularInclusion :=
  triangleOpenInclusion_isOpenEmbedding.comp triangleRegularToOrbit_isOpenEmbedding

theorem regularInclusion_mem (q : TriangleRegularQuotient) :
    regularInclusion q ∈ regularPatch := by
  apply (openInclusion_mem_regularPatch_iff (triangleRegularToOrbit q)).mpr
  exact mem_range_self q

/-- The regular inclusion has precisely the three-puncture complement as
its image, not merely an unspecified open image. -/
theorem regularInclusion_range :
    range regularInclusion = (regularPatch : Set TriangleCompactifiedOrbitSpace) := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact regularInclusion_mem q
  · intro hx
    obtain ⟨q, hq⟩ := OnePoint.ne_infty_iff_exists.mp ((mem_regularPatch x).mp hx).1
    have hq' : triangleOpenInclusion q = x := hq
    have hreg : q ∈ triangleOrbitRegularDomain :=
      (openInclusion_mem_regularPatch_iff q).mp (hq' ▸ hx)
    obtain ⟨r, hr⟩ := hreg
    exact ⟨r, (congrArg triangleOpenInclusion hr).trans hq'⟩

/-- The inclusion is locally biholomorphic for the established regular,
full-orbit, and compact-curve atlases. -/
theorem regularInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω regularInclusion := by
  intro q
  have hreg : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularToOrbit q :=
    (triangleRegularOrbitBiholomorph.isLocalDiffeomorph q).comp
      (K := 𝓘(ℂ)) (P := TriangleOrbitSpace)
      (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) triangleOrbitRegularDomain
        (triangleRegularOrbitBiholomorph q))
  exact hreg.comp (K := 𝓘(ℂ)) (P := TriangleCompactifiedOrbitSpace)
    (triangleOpenInclusion_isLocalDiffeomorph (triangleRegularToOrbit q))

theorem regularInclusion_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω regularInclusion :=
  regularInclusion_isLocalDiffeomorph.contMDiff

/-- Restrict only the target of the actual regular inclusion. -/
def regularInclusionToPatch (q : TriangleRegularQuotient) : regularPatch :=
  ⟨regularInclusion q, regularInclusion_mem q⟩

@[simp] theorem regularInclusionToPatch_coe (q : TriangleRegularQuotient) :
    (regularInclusionToPatch q : TriangleCompactifiedOrbitSpace) = regularInclusion q := rfl

theorem regularInclusionToPatch_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω regularInclusionToPatch :=
  isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ)
    regularInclusion_isLocalDiffeomorph regularPatch regularInclusion_mem

theorem regularInclusionToPatch_bijective : Bijective regularInclusionToPatch := by
  constructor
  · intro q r h
    exact regularInclusion_isOpenEmbedding.injective (congrArg Subtype.val h)
  · intro x
    have hx : x.val ∈ range regularInclusion := by
      rw [regularInclusion_range]
      exact x.property
    obtain ⟨q, hq⟩ := hx
    exact ⟨q, Subtype.ext hq⟩

/-- The actual regular covering quotient is biholomorphic to the literal
three-puncture open subset of the constructed compact triangle curve. -/
def regularBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleRegularQuotient regularPatch ω :=
  regularInclusionToPatch_isLocalDiffeomorph.diffeomorphOfBijective
    regularInclusionToPatch_bijective

@[simp] theorem regularBiholomorph_coe (q : TriangleRegularQuotient) :
    (regularBiholomorph q : TriangleCompactifiedOrbitSpace) = regularInclusion q := rfl

@[simp] theorem regularBiholomorph_project (z : TriangleRegularPoint) :
    (regularBiholomorph (triangleRegularProject z) : TriangleCompactifiedOrbitSpace) =
      triangleCompactifiedProjection z.val := rfl

@[simp] theorem regularBiholomorph_symm_coe (x : regularPatch) :
    regularInclusion (regularBiholomorph.symm x) = x :=
  congrArg Subtype.val (regularBiholomorph.apply_symm_apply x)

/-- The same actual base identification as a homeomorphism. -/
def regularHomeomorph : TriangleRegularQuotient ≃ₜ regularPatch :=
  regularBiholomorph.toHomeomorph

/-- The native regular quotient projection with target the compact base patch. -/
def regularProjection : TriangleRegularPoint → regularPatch :=
  regularBiholomorph ∘ triangleRegularProject

@[simp] theorem regularProjection_coe (z : TriangleRegularPoint) :
    (regularProjection z : TriangleCompactifiedOrbitSpace) =
      triangleCompactifiedProjection z.val := rfl

theorem regularProjection_surjective : Surjective regularProjection :=
  regularBiholomorph.surjective.comp triangleRegularProject_surjective

theorem regularProjection_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω regularProjection := by
  intro z
  exact (triangleRegularProject_isLocalDiffeomorph z).comp
    (K := 𝓘(ℂ)) (P := regularPatch)
    (regularBiholomorph.isLocalDiffeomorph (triangleRegularProject z))

theorem regularProjection_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω regularProjection :=
  regularProjection_isLocalDiffeomorph.contMDiff

/-- Equality in the regular patch is exactly the original triangle orbit
relation on the upper-half-plane representatives. -/
theorem regularProjection_eq_iff (z w : TriangleRegularPoint) :
    regularProjection z = regularProjection w ↔
      ∃ g : TriangleGroup, triangleGeometricRepresentation g w.val = z.val := by
  rw [← triangleCompactifiedProjection_eq_iff z.val w.val]
  exact Subtype.ext_iff

theorem regularPatch_inclusion_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val : regularPatch → TriangleCompactifiedOrbitSpace) :=
  contMDiff_subtype_val

theorem regularPatch_inclusion_isOpenEmbedding :
    IsOpenEmbedding (Subtype.val : regularPatch → TriangleCompactifiedOrbitSpace) :=
  regularPatch.isOpen.isOpenEmbedding_subtypeVal

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
