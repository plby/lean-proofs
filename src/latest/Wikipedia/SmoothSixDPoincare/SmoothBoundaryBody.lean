import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyAttach
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Compact bodies with their actual embedded native smooth boundaries

These records bundle the topology, native atlas, and closed boundary
embedding needed to compose finite framed attachments. A body is only
topological; its specified boundary is a smooth manifold in the common
model. A framed attachment supplies all fields from the proved quotient
and boundary constructions.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  (J : ModelWithCorners ℝ G H)

structure SmoothBoundaryBody where
  boundary : TopCat.{0}
  charted : ChartedSpace H boundary
  smooth : letI := charted; IsManifold J ∞ boundary
  boundaryT2 : T2Space boundary
  boundaryCompact : CompactSpace boundary
  body : TopCat.{0}
  bodyT2 : T2Space body
  bodyCompact : CompactSpace body
  inclusion : C(boundary, body)
  closedEmbedding : IsClosedEmbedding inclusion

attribute [instance] SmoothBoundaryBody.charted SmoothBoundaryBody.smooth
  SmoothBoundaryBody.boundaryT2 SmoothBoundaryBody.boundaryCompact
  SmoothBoundaryBody.bodyT2 SmoothBoundaryBody.bodyCompact

namespace SmoothBoundaryBody

variable {J}

def ofEmbedding {X Y : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace H X] [IsManifold J ∞ X] [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    (i : C(X, Y)) (hi : IsClosedEmbedding i) : SmoothBoundaryBody J where
  boundary := TopCat.of X
  charted := inferInstance
  smooth := inferInstance
  boundaryT2 := inferInstance
  boundaryCompact := inferInstance
  body := TopCat.of Y
  bodyT2 := inferInstance
  bodyCompact := inferInstance
  inclusion := i
  closedEmbedding := hi

abbrev Equiv (U V : SmoothBoundaryBody J) :=
  SmoothBoundaryBodyEquiv (J := J) U.inclusion V.inclusion

variable (U : SmoothBoundaryBody J)
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (PuncturedHandle.UnitSphere E) F U.boundary)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]
  (P : FramedSurgery.SmoothBoundaryData A n)

def attach : SmoothBoundaryBody J where
  boundary := TopCat.of (FramedSurgery.Boundary A n)
  charted := P.charted
  smooth := P.smooth
  boundaryT2 := inferInstance
  boundaryCompact := inferInstance
  body := TopCat.of (FramedSurgery.AttachedBody A U.inclusion)
  bodyT2 := FramedSurgery.attachedBodyT2Space A U.inclusion U.closedEmbedding.injective
  bodyCompact := inferInstance
  inclusion := FramedSurgery.boundaryBodyMap A U.inclusion n U.closedEmbedding
  closedEmbedding :=
    FramedSurgery.boundaryBodyMap_isClosedEmbedding A U.inclusion n U.closedEmbedding

theorem attach_inclusion :
    (U.attach A n P).inclusion =
      FramedSurgery.boundaryBodyMap A U.inclusion n U.closedEmbedding := rfl

end SmoothBoundaryBody

end Wikipedia.SmoothSixDPoincare
