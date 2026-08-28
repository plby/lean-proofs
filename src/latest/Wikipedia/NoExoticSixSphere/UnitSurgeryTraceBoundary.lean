import Wikipedia.NoExoticSixSphere.UnitSurgeryComparisonDiffeomorph

/-!
# The native trace boundary is the original manifold plus actual surgery

This smooth identification keeps the original manifold atlas, the native
rounded-trace boundary atlas, and the canonical surgery atlas. It also proves
compactness of the actual surgery target. Boundary normal framings require
an additional outward-normal construction and are not inferred here.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedHandleCorner RoundedTrace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem compactSpace_target : CompactSpace (Target A hR) := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  let := compactSpace_otherBoundaryPart A
  exact (surjective_comparisonMap A hR).compactSpace (contMDiff_comparisonMap A hR).continuous

def traceBoundaryDiffeomorph : letI := boundaryChartedSpace A;
    letI := targetChartedSpace A hR;
    (M ⊕ Target A hR) ≃ₘ⟮𝓡 6, 𝓡 6⟯ Boundary A := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  exact ((Diffeomorph.refl (𝓡 6) M ∞).sumCongr (comparisonDiffeomorph A hR).symm).trans
    (boundaryEndsDiffeomorph A)

theorem traceBoundaryDiffeomorph_inl (m : M) :
    letI := boundaryChartedSpace A; letI := targetChartedSpace A hR;
    (traceBoundaryDiffeomorph A hR (Sum.inl m)).val.val =
      e.heightCylinder (m, UnroundedTrace.height A) := rfl

theorem traceBoundaryDiffeomorph_inr (p : Target A hR) :
    letI := boundaryChartedSpace A; letI := targetChartedSpace A hR;
    traceBoundaryDiffeomorph A hR (Sum.inr p) = ((comparisonDiffeomorph A hR).symm p).val := rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
