import Wikipedia.HopfProblem.DegreeCollapseSevenUnitSurgeryComparisonDiffeomorph

/-!
# The native trace boundary is the original manifold plus actual surgery

This smooth identification keeps the original manifold atlas, the native
rounded-trace boundary atlas, and the canonical surgery atlas. It also proves
compactness of the actual surgery target. The existing outward normal is retained; transporting its induced
normal frame to the canonical target is a separate step.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner RoundedTrace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem compactSpace_target : CompactSpace (Target A hR) := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  let := compactSpace_otherBoundaryPart A
  exact (surjective_comparisonMap A hR).compactSpace (contMDiff_comparisonMap A hR).continuous

def traceBoundaryDiffeomorph : letI := boundaryChartedSpace A;
    letI := targetChartedSpace A hR;
    (M ⊕ Target A hR) ≃ₘ⟮𝓡 7, 𝓡 7⟯ Boundary A := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  exact ((Diffeomorph.refl (𝓡 7) M ∞).sumCongr (comparisonDiffeomorph A hR).symm).trans
    (boundaryEndsDiffeomorph A)

theorem traceBoundaryDiffeomorph_inl (m : M) :
    letI := boundaryChartedSpace A; letI := targetChartedSpace A hR;
    (traceBoundaryDiffeomorph A hR (Sum.inl m)).val.val =
      (HeightCylinder.heightCylinder e) (m, UnroundedTrace.height A) := rfl

theorem traceBoundaryDiffeomorph_inr (p : Target A hR) :
    letI := boundaryChartedSpace A; letI := targetChartedSpace A hR;
    traceBoundaryDiffeomorph A hR (Sum.inr p) = ((comparisonDiffeomorph A hR).symm p).val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
