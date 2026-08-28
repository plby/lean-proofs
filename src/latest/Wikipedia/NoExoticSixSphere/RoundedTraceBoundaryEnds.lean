import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryDifferential
import Wikipedia.NoExoticSixSphere.ClopenDiffeomorph

/-!
# Compact smooth ends of the actual rounded trace

The complementary end is defined as an actual open-and-closed subset of the
native boundary, with its inherited six-dimensional atlas. Splitting along
the original end gives a diffeomorphism from the disjoint union of the
original manifold and this complementary end onto the full boundary.
Identifying the complementary end with surgery is a separate obligation.
-/

noncomputable section

open Function Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem isClosed_nativeBoundary : letI := traceChartedSpace A;
    IsClosed {p : ambientSet A | (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p} := by
  let := traceChartedSpace A
  let := trace_isManifold A
  exact (ProductHalfSpace.model (Vector 6)).isClosed_boundary (n := ∞) (by simp)

theorem compactSpace_boundary : CompactSpace (Boundary A) := by
  let := isCompact_iff_compactSpace.mp (isCompact_ambientSet A)
  exact isCompact_iff_compactSpace.mp (isClosed_nativeBoundary A).isCompact

theorem isClosedEmbedding_boundaryAmbient :
    IsClosedEmbedding (fun p : Boundary A ↦ p.val.val) :=
  (isClosed_ambientSet A).isClosedEmbedding_subtypeVal.comp
    (isClosed_nativeBoundary A).isClosedEmbedding_subtypeVal

def boundaryEuclideanEmbedding : letI := boundaryChartedSpace A;
    EuclideanEmbedding 6 (Boundary A) := by
  let := boundaryChartedSpace A
  exact
    { ambientDimension := e.ambientDimension + 6
      toFun := fun p ↦ p.val.val
      smooth := contMDiff_boundaryAmbientInclusion A
      closedEmbedding := isClosedEmbedding_boundaryAmbient A
      injective_mfderiv := injective_boundaryAmbientDerivative A }

def otherBoundaryPart : Opens (Boundary A) :=
  clopenComplement (topBoundaryPart A) (isClosed_topBoundaryPart A)

theorem mem_otherBoundaryPart_iff (p : Boundary A) :
    p ∈ otherBoundaryPart A ↔ p.val ∉ topEnd A :=
  not_congr (mem_topBoundaryPart_iff A p)

theorem isClosed_otherBoundaryPart : IsClosed (otherBoundaryPart A : Set (Boundary A)) :=
  (topBoundaryPart A).isOpen.isClosed_compl

theorem compactSpace_otherBoundaryPart : CompactSpace (otherBoundaryPart A) := by
  let := compactSpace_boundary A
  exact isCompact_iff_compactSpace.mp (isClosed_otherBoundaryPart A).isCompact

theorem otherBoundary_isManifold : letI := boundaryChartedSpace A;
    IsManifold (𝓡 6) ∞ (otherBoundaryPart A) := by
  let := boundaryChartedSpace A
  let := boundary_isManifold A
  infer_instance

def boundaryEndsDiffeomorph : letI := boundaryChartedSpace A;
    (M ⊕ otherBoundaryPart A) ≃ₘ⟮𝓡 6, 𝓡 6⟯ Boundary A := by
  let := boundaryChartedSpace A
  exact ((originalBoundaryDiffeomorph A).sumCongr
    (Diffeomorph.refl (𝓡 6) (otherBoundaryPart A) ∞)).trans
      (clopenDiffeomorph (I := 𝓡 6) (topBoundaryPart A) (isClosed_topBoundaryPart A))

theorem boundaryEndsDiffeomorph_inl (m : M) : letI := boundaryChartedSpace A;
    (boundaryEndsDiffeomorph A (Sum.inl m)).val.val =
      e.heightCylinder (m, UnroundedTrace.height A) := rfl

theorem boundaryEndsDiffeomorph_inr (p : otherBoundaryPart A) :
    letI := boundaryChartedSpace A;
    boundaryEndsDiffeomorph A (Sum.inr p) = p.val := rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
