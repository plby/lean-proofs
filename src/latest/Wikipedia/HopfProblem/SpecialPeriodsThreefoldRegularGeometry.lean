import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Wikipedia.HopfProblem.CoveringSubmersion

/-!
# The native regular geometry of the actual compact threefold

The full inverse image of the regular compact-base patch is the original
special-period torus family, with its original quotient atlas.  The
inclusion is locally biholomorphic.  A commuting square with the actual
regular base inclusion transports the proved submersion normal form to
the constructed global map to the sphere, retaining its two-dimensional
complex complement.
-/

noncomputable section

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle TrianglePeriodFamily

attribute [local instance] triangleCompactifiedChartedSpace triangleRegularQuotientChartedSpace
  chartedSpace specialRegularFamilyChartedSpace localPieceChartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "Dreg" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
local notation "hqreg" =>
  regularCovering specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The actual full regular part of the assembled threefold. -/
abbrev regularLocus : Opens Space := liftedPatch none

@[simp] theorem mem_regularLocus (y : Space) :
    y ∈ regularLocus ↔ projection y ∈ regularPatch := Iff.rfl

theorem regularLocus_eq_preimage :
    (regularLocus : Set Space) = projection ⁻¹'
      (regularPatch : Set TriangleCompactifiedOrbitSpace) := rfl

/-- The genuine regular-family inclusion into the constructed threefold. -/
def regularFamilyInclusion : SpecialRegularFamily → Space := inclusion none

@[simp] theorem regularFamilyInclusion_eq (x : SpecialRegularFamily) :
    regularFamilyInclusion x = inclusion none x := rfl

/-- The original regular quotient family is biholomorphic to the entire
regular locus, with both existing native atlases unchanged. -/
def regularFamilyBiholomorph :
    Diffeomorph IF IF SpecialRegularFamily regularLocus ω := patchBiholomorph none

/-- The inverse orientation identifies the actual global open locus
with the original regular period family. -/
def regularLocusBiholomorph :
    Diffeomorph IF IF regularLocus SpecialRegularFamily ω := regularFamilyBiholomorph.symm

@[simp] theorem regularFamilyBiholomorph_val (x : SpecialRegularFamily) :
    (regularFamilyBiholomorph x : Space) = regularFamilyInclusion x := rfl

@[simp] theorem regularLocusBiholomorph_inclusion (x : regularLocus) :
    regularFamilyInclusion (regularLocusBiholomorph x) = (x : Space) :=
  congrArg Subtype.val (regularFamilyBiholomorph.apply_symm_apply x)

@[simp] theorem regularFamilyInclusion_projection (x : SpecialRegularFamily) :
    projection (regularFamilyInclusion x) = specialRegularFamilyProjectionToBase x :=
  projection_inclusion none x

theorem regularFamilyBiholomorph_projection (x : SpecialRegularFamily) :
    projection (regularFamilyBiholomorph x) = specialRegularFamilyProjectionToBase x :=
  regularFamilyInclusion_projection x

theorem regularLocusBiholomorph_projection (x : regularLocus) :
    specialRegularFamilyProjectionToBase (regularLocusBiholomorph x) = projection x :=
  (regularFamilyInclusion_projection (regularLocusBiholomorph x)).symm.trans
    (congrArg projection (regularLocusBiholomorph_inclusion x))

/-- The same inclusion preserves the original regular quotient coordinate. -/
theorem regularFamilyInclusion_projection_quotient (x : SpecialRegularFamily) :
    projection (regularFamilyInclusion x) = regularInclusion ((Dreg).projection x) :=
  regularFamilyInclusion_projection x

theorem regularFamilyInclusion_isOpenEmbedding : IsOpenEmbedding regularFamilyInclusion :=
  inclusion_openEmbedding none

theorem range_regularFamilyInclusion :
    range regularFamilyInclusion = (regularLocus : Set Space) := inclusion_range none

/-- Local biholomorphy follows from the actual patch biholomorphism and
the ordinary open-submanifold inclusion. -/
theorem regularFamilyInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph IF IF ω regularFamilyInclusion := by
  intro x
  exact (regularFamilyBiholomorph.isLocalDiffeomorph x).comp (K := IF) (P := Space)
    (isLocalDiffeomorph_subtypeVal IF regularLocus (regularFamilyBiholomorph x))

theorem regularFamilyInclusion_holomorphic : ContMDiff IF IF ω regularFamilyInclusion :=
  regularFamilyInclusion_isLocalDiffeomorph.contMDiff

/-- The native regular quotient mapped to the actual normalized sphere. -/
def regularBaseSphere : TriangleRegularQuotient → RiemannSphere :=
  triangleSphereUniformization ∘ regularInclusion

theorem regularBaseSphere_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω regularBaseSphere := by
  intro q
  exact (regularInclusion_isLocalDiffeomorph q).comp (K := 𝓘(ℂ)) (P := RiemannSphere)
    (triangleSphereUniformization.isLocalDiffeomorph (regularInclusion q))

/-- The actual projection square commutes, without any change of periods
or of the regular base coordinate. -/
theorem regularFamilyInclusion_projectionSphere (x : SpecialRegularFamily) :
    projectionSphere (regularFamilyInclusion x) = regularBaseSphere ((Dreg).projection x) :=
  projectionSphere_inclusion none x

theorem regularFamilyBiholomorph_projectionSphere (x : SpecialRegularFamily) :
    projectionSphere (regularFamilyBiholomorph x) =
      triangleSphereUniformization (specialRegularFamilyProjectionToBase x) :=
  projectionSphere_inclusion none x

theorem regularLocusBiholomorph_projectionSphere (x : regularLocus) :
    triangleSphereUniformization
        (specialRegularFamilyProjectionToBase (regularLocusBiholomorph x)) =
      projectionSphere x :=
  congrArg triangleSphereUniformization (regularLocusBiholomorph_projection x)

/-- Transport the actual regular-family submersion normal form through
the locally biholomorphic inclusion square, keeping `ComplexPlane₂`. -/
theorem projectionSphere_submersionAt_regularFamily (x : SpecialRegularFamily) :
    Manifold.IsSubmersionAtOfComplement ComplexPlane₂ IF 𝓘(ℂ) ω projectionSphere
      (regularFamilyInclusion x) := by
  let := space_isManifold
  exact submersionAt_of_localDiffeomorph_square
    (regularFamilyInclusion_isLocalDiffeomorph x)
    (regularBaseSphere_isLocalDiffeomorph ((Dreg).projection x))
    ((Dreg).projection_submersion hqreg x) regularFamilyInclusion_projectionSphere

/-- Every point of the actual full regular locus has the proved global
submersion normal form. -/
theorem projectionSphere_submersionAt_regular (y : Space) (hy : projection y ∈ regularPatch) :
    Manifold.IsSubmersionAtOfComplement ComplexPlane₂ IF 𝓘(ℂ) ω projectionSphere y := by
  obtain ⟨x, hx⟩ := regularFamilyBiholomorph.surjective (⟨y, hy⟩ : regularLocus)
  have hx' : regularFamilyInclusion x = y := congrArg Subtype.val hx
  rw [← hx']
  exact projectionSphere_submersionAt_regularFamily x

/-- The literal sphere with its three normalized marked values removed. -/
def sphereRegularPatch : Opens RiemannSphere :=
  ⟨({(∞ : RiemannSphere), ((0 : ℂ) : RiemannSphere), ((1 : ℂ) : RiemannSphere)} :
      Set RiemannSphere)ᶜ,
    (((finite_singleton ((1 : ℂ) : RiemannSphere)).insert
      ((0 : ℂ) : RiemannSphere)).insert (∞ : RiemannSphere)).isClosed.isOpen_compl⟩

@[simp] theorem mem_sphereRegularPatch (b : RiemannSphere) :
    b ∈ sphereRegularPatch ↔ b ≠ (∞ : RiemannSphere) ∧ b ≠ ((0 : ℂ) : RiemannSphere) ∧
      b ≠ ((1 : ℂ) : RiemannSphere) := by
  simp only [sphereRegularPatch, Opens.mem_mk, mem_compl_iff, mem_insert_iff,
    mem_singleton_iff, not_or]

/-- The actual normalized uniformization identifies precisely the two
three-puncture complements. -/
@[simp] theorem sphereUniformization_mem_regular_iff (q : TriangleCompactifiedOrbitSpace) :
    triangleSphereUniformization q ∈ sphereRegularPatch ↔ q ∈ regularPatch := by
  rw [mem_sphereRegularPatch, mem_regularPatch]
  have h₁ : triangleSphereUniformization triangleCompactifiedCenterOne =
      ((0 : ℂ) : RiemannSphere) := triangleSphereUniformization_centerOne
  have h₂ : triangleSphereUniformization triangleCompactifiedCenterTwo =
      ((1 : ℂ) : RiemannSphere) := triangleSphereUniformization_centerTwo
  rw [← triangleSphereUniformization_cusp, ← h₁, ← h₂]
  have hinj : Function.Injective triangleSphereUniformization :=
    triangleSphereUniformization.injective
  simp only [ne_eq, hinj.eq_iff]

theorem sphereUniformization_preimage_regularPatch :
    triangleSphereUniformization ⁻¹' (sphereRegularPatch : Set RiemannSphere) =
      (regularPatch : Set TriangleCompactifiedOrbitSpace) := by
  ext q
  exact sphereUniformization_mem_regular_iff q

@[simp] theorem projectionSphere_mem_sphereRegularPatch (y : Space) :
    projectionSphere y ∈ sphereRegularPatch ↔ projection y ∈ regularPatch :=
  sphereUniformization_mem_regular_iff (projection y)

theorem mem_regularLocus_iff_sphere (y : Space) :
    y ∈ regularLocus ↔ projectionSphere y ∈ sphereRegularPatch :=
  (projectionSphere_mem_sphereRegularPatch y).symm

theorem regularLocus_eq_sphere_preimage :
    (regularLocus : Set Space) = projectionSphere ⁻¹' (sphereRegularPatch : Set RiemannSphere) :=
  Set.ext mem_regularLocus_iff_sphere

theorem projectionSphere_submersionAt_of_mem_sphereRegularPatch (y : Space)
    (hy : projectionSphere y ∈ sphereRegularPatch) :
    Manifold.IsSubmersionAtOfComplement ComplexPlane₂ IF 𝓘(ℂ) ω projectionSphere y :=
  projectionSphere_submersionAt_regular y ((projectionSphere_mem_sphereRegularPatch y).mp hy)

/-- The actual global sphere projection is a submersion, with complex
two-plane complement, away from the three specified marked values. -/
theorem projectionSphere_submersionAt_of_ne (y : Space)
    (h_infty : projectionSphere y ≠ (∞ : RiemannSphere))
    (h₀ : projectionSphere y ≠ ((0 : ℂ) : RiemannSphere))
    (h₁ : projectionSphere y ≠ ((1 : ℂ) : RiemannSphere)) :
    Manifold.IsSubmersionAtOfComplement ComplexPlane₂ IF 𝓘(ℂ) ω projectionSphere y :=
  projectionSphere_submersionAt_of_mem_sphereRegularPatch y
    ((mem_sphereRegularPatch (projectionSphere y)).mpr ⟨h_infty, h₀, h₁⟩)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
