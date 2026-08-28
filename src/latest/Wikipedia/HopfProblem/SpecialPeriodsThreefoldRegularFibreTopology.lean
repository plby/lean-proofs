import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Wikipedia.HopfProblem.TrianglePeriodFamilyFibres

/-!
# The actual regular fibres of the unconditional threefold

The complex period torus at a genuine regular upper-half-plane point
includes in the glued threefold through its original regular-family
piece. Its image is the entire literal sphere fibre. The resulting
homeomorphism preserves the actual quotient and subspace topologies;
no complex structure is transported onto the fibre in this file.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle

attribute [local instance] chartedSpace localPieceChartedSpace space_t2Space

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The original complex torus of the actual special period at a regular point. -/
abbrev RegularTorus (z : TriangleRegularPoint) := (specialPeriodMap.point z.val).Torus

/-- The corresponding value in the actual normalized sphere base. -/
def regularSphereValue (z : TriangleRegularPoint) : RiemannSphere :=
  triangleSphereUniformization (triangleCompactifiedProjection z.val)

/-- The actual period torus inclusion, through the original regular quotient
piece and its open inclusion into the glued threefold. -/
def regularTorusInclusion (z : TriangleRegularPoint) : RegularTorus z → Space :=
  inclusion none ∘
    (regularFamilyData specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂).fibreInclusion z

@[simp] theorem projection_regularTorusInclusion (z : TriangleRegularPoint)
    (x : RegularTorus z) :
    projection (regularTorusInclusion z x) = triangleCompactifiedProjection z.val := by
  let D := regularFamilyData specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂
  exact (projection_inclusion none (D.fibreInclusion z x)).trans
    (regularFamilyProjectionToBase_quotient specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ (D.periods.fibreInclusion z x))

@[simp] theorem projectionSphere_regularTorusInclusion (z : TriangleRegularPoint)
    (x : RegularTorus z) :
    projectionSphere (regularTorusInclusion z x) = regularSphereValue z := by
  change triangleSphereUniformization (projection (regularTorusInclusion z x)) = _
  rw [projection_regularTorusInclusion]
  rfl

theorem regularTorusInclusion_continuous (z : TriangleRegularPoint) :
    Continuous (regularTorusInclusion z) :=
  (inclusion_openEmbedding none).continuous.comp
    ((regularFamilyData specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂).fibreInclusion_continuous z)

theorem regularTorusInclusion_injective (z : TriangleRegularPoint) :
    Function.Injective (regularTorusInclusion z) :=
  (inclusion_openEmbedding none).injective.comp
    ((regularFamilyData specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂).fibreInclusion_injective
        (TrianglePeriodFamily.regularCovering specialPeriodMap specialPeriodMap_generator₁
          specialPeriodMap_generator₂) z)

/-- Compactness of the actual period torus makes its genuine inclusion closed. -/
theorem regularTorusInclusion_isClosedEmbedding (z : TriangleRegularPoint) :
    IsClosedEmbedding (regularTorusInclusion z) :=
  (regularTorusInclusion_continuous z).isClosedEmbedding (regularTorusInclusion_injective z)

theorem regularTorusInclusion_isEmbedding (z : TriangleRegularPoint) :
    IsEmbedding (regularTorusInclusion z) :=
  (regularTorusInclusion_isClosedEmbedding z).isEmbedding

/-- Holomorphicity uses the original period-torus, regular-family, and
glued-manifold atlases throughout. -/
theorem regularTorusInclusion_holomorphic (z : TriangleRegularPoint) :
    ContMDiff I₂ IF ω (regularTorusInclusion z) :=
  (inclusion_holomorphic none).comp
    ((regularFamilyData specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂).fibreInclusion_holomorphic
        (TrianglePeriodFamily.regularCovering specialPeriodMap specialPeriodMap_generator₁
          specialPeriodMap_generator₂) z)

/-- The inclusion reaches the whole literal global sphere fibre, with
no extra points coming from any of the other glued pieces. -/
theorem regularTorusInclusion_range (z : TriangleRegularPoint) :
    range (regularTorusInclusion z) = projectionSphere ⁻¹' {regularSphereValue z} := by
  let D := regularFamilyData specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact projectionSphere_regularTorusInclusion z x
  · intro hy
    have hyproj : projection y = triangleCompactifiedProjection z.val :=
      triangleSphereUniformization.injective hy
    have hyregular : y ∈ range (inclusion none) := by
      rw [inclusion_range]
      change projection y ∈ regularPatch
      rw [hyproj, ← regularInclusion_project z]
      exact regularInclusion_mem (triangleRegularProject z)
    obtain ⟨a, ha⟩ := hyregular
    have hae : regularInclusion (D.projection a) = projection y := by
      rw [← ha, projection_inclusion]
      rfl
    have hpa : D.projection a = D.baseQuotient z :=
      regularInclusion_isOpenEmbedding.injective
        (hae.trans (hyproj.trans (regularInclusion_project z).symm))
    have harange : a ∈ range (D.fibreInclusion z) := by
      rw [D.fibreInclusion_range
        (TrianglePeriodFamily.regularCovering specialPeriodMap specialPeriodMap_generator₁
          specialPeriodMap_generator₂)]
      exact hpa
    obtain ⟨x, rfl⟩ := harange
    exact ⟨x, ha⟩

/-- The original period torus is homeomorphic to the entire actual regular
sphere fibre, carrying the inherited subspace topology. -/
def regularTorusFibreHomeomorph (z : TriangleRegularPoint) :
    RegularTorus z ≃ₜ (projectionSphere ⁻¹' {regularSphereValue z}) :=
  (regularTorusInclusion_isEmbedding z).toHomeomorph.trans
    (Homeomorph.setCongr (regularTorusInclusion_range z))

@[simp] theorem regularTorusFibreHomeomorph_coe (z : TriangleRegularPoint)
    (x : RegularTorus z) :
    (regularTorusFibreHomeomorph z x : Space) = regularTorusInclusion z x := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
