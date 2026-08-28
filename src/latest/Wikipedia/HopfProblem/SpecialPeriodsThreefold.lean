import Wikipedia.HopfProblem.SpecialPeriodsThreefoldOverlaps
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRestrictionProper
import Wikipedia.HopfProblem.ThreefoldGluingConstruction

/-!
# The actual compact complex threefold over the sphere

The genuine global special periods, the two main twisted elliptic
fillings, and the full toric cusp quotient give the four local pieces.
Their full overlaps have been constructed and checked, so the gluing
below has no period, uniformization, filling, or compatibility inputs.

The constructed space is compact, Hausdorff, second countable, and a
complex manifold with three-dimensional model.  Its proper surjective
holomorphic map to the sphere restricts to the original local maps via
actual biholomorphisms with the full inverse images of the base patches.
-/

noncomputable section

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle

attribute [local instance] triangleCompactifiedChartedSpace localPieceChartedSpace
  localPiece_nonempty localPiece_t2Space localPiece_secondCountable localPiece_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual gluing of the regular family and the three constructed fillings. -/
abbrev Space := gluingData.Space

/-- The complex atlas transported from the genuine local pieces. -/
@[instance_reducible] def chartedSpace : ChartedSpace (ℂ × ComplexPlane₂) Space :=
  gluingData.chartedSpace

attribute [local instance] chartedSpace

/-- The actual projection to the compactified triangle quotient. -/
abbrev projection : Space → TriangleCompactifiedOrbitSpace := gluingData.projection

theorem projection_continuous : Continuous projection := gluingData.projection_continuous

theorem projection_proper : IsProperMap projection :=
  gluingData.projection_proper gluingData_localProjection_proper

theorem projection_surjective : Function.Surjective projection :=
  gluingData.projection_surjective gluingData_localProjection_surjective

theorem projection_holomorphic : ContMDiff IF 𝓘(ℂ) ω projection :=
  gluingData.projection_holomorphic localProjectionToBase_holomorphic

/-- Compactness follows from the proved proper local maps over the actual compact base. -/
theorem space_compact : CompactSpace Space :=
  gluingData.compactSpace gluingData_localProjection_proper

theorem space_t2Space : T2Space Space := gluingData.spaceT2

theorem space_secondCountable : SecondCountableTopology Space :=
  gluingData.secondCountableSpace_of_compactBase

theorem space_isManifold : IsManifold IF ω Space :=
  gluingData.isManifold gluingData_transition_holomorphic

theorem space_nonempty : Nonempty Space :=
  ⟨gluingData.inclusion none specialRegularFamilyPoint⟩

/-- The model has complex dimension exactly three. -/
theorem complex_dimension : Module.finrank ℂ (ℂ × ComplexPlane₂) = 3 := by
  simp [ComplexPlane₂, Module.finrank_prod]

/-- The holomorphic map to the sphere uses the constructed, normalized
biholomorphism of the actual compactified triangle quotient. -/
def projectionSphere : Space → RiemannSphere := triangleSphereUniformization ∘ projection

theorem projectionSphere_continuous : Continuous projectionSphere :=
  triangleSphereUniformization.continuous.comp projection_continuous

theorem projectionSphere_proper : IsProperMap projectionSphere :=
  triangleSphereUniformization.toHomeomorph.isProperMap.comp projection_proper

theorem projectionSphere_surjective : Function.Surjective projectionSphere :=
  triangleSphereUniformization.surjective.comp projection_surjective

theorem projectionSphere_holomorphic : ContMDiff IF 𝓘(ℂ) ω projectionSphere :=
  triangleSphereUniformization.contMDiff.comp projection_holomorphic

/-- The original pieces include as full open subsets of the glued manifold. -/
abbrev inclusion (i : Index) : localPiece i → Space := gluingData.inclusion i

theorem inclusion_openEmbedding (i : Index) : Topology.IsOpenEmbedding (inclusion i) :=
  gluingData.inclusion_openEmbedding i

theorem inclusion_holomorphic (i : Index) : ContMDiff IF IF ω (inclusion i) :=
  gluingData.inclusion_holomorphic gluingData_transition_holomorphic i

@[simp] theorem projection_inclusion (i : Index) (x : localPiece i) :
    projection (inclusion i x) = localProjectionToBase i x :=
  gluingData.projection_inclusion i x

theorem projectionSphere_inclusion (i : Index) (x : localPiece i) :
    projectionSphere (inclusion i x) =
      triangleSphereUniformization (localProjectionToBase i x) :=
  congrArg triangleSphereUniformization (projection_inclusion i x)

theorem inclusion_range (i : Index) :
    range (inclusion i) = projection ⁻¹'
      (specialBaseCover.patch i : Set TriangleCompactifiedOrbitSpace) :=
  gluingData.inclusion_range i

/-- The full inverse image of a member of the actual four-patch cover. -/
abbrev liftedPatch (i : Index) : Opens Space := gluingData.liftedPatch i

/-- Each genuine local piece is biholomorphic to that full inverse image,
not merely to a smaller neighborhood of its central fibre. -/
def patchBiholomorph (i : Index) :
    Diffeomorph IF IF (localPiece i) (liftedPatch i) ω :=
  gluingData.patchBiholomorph gluingData_transition_holomorphic i

@[simp] theorem patchBiholomorph_val (i : Index) (x : localPiece i) :
    (patchBiholomorph i x).val = inclusion i x := rfl

theorem patchBiholomorph_projection (i : Index) (x : localPiece i) :
    projection (patchBiholomorph i x) = localProjectionToBase i x :=
  projection_inclusion i x

theorem projection_fibre_compact (b : TriangleCompactifiedOrbitSpace) :
    IsCompact (projection ⁻¹' {b}) :=
  projection_proper.isCompact_preimage isCompact_singleton

theorem projectionSphere_fibre_compact (b : RiemannSphere) :
    IsCompact (projectionSphere ⁻¹' {b}) :=
  projectionSphere_proper.isCompact_preimage isCompact_singleton

/-- The unconditional compact holomorphic threefold construction.  All
local geometry, all overlaps, and the normalized sphere map used here
are the constructed ones; there are no mathematical premises. -/
theorem compact_holomorphic_threefold :
    CompactSpace Space ∧ T2Space Space ∧ SecondCountableTopology Space ∧
      IsManifold IF ω Space ∧ Module.finrank ℂ (ℂ × ComplexPlane₂) = 3 ∧
      IsProperMap projectionSphere ∧ Function.Surjective projectionSphere ∧
      ContMDiff IF 𝓘(ℂ) ω projectionSphere :=
  ⟨space_compact, space_t2Space, space_secondCountable, space_isManifold,
    complex_dimension, projectionSphere_proper, projectionSphere_surjective,
    projectionSphere_holomorphic⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
