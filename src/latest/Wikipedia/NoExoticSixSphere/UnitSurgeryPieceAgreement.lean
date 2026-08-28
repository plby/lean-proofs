import Wikipedia.NoExoticSixSphere.UnitSurgerySmoothMaps
import Wikipedia.NoExoticSixSphere.RoundedTraceSurgeryOverlaps

/-!
# Canonical surgery maps agree at actual common boundary points

The overlap tests recover the appropriate collar parameter inequality from
equality in the actual native boundary. The ambient overlap identities then
identify the coordinates used by the two canonical surgery maps.
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

theorem collar_handle_agreement (p : boundaryCollarParameters A)
    (q : boundaryPieceDomain A .handle) :
    letI := boundaryPieceAtlas A .collar; letI := boundaryPieceAtlas A .handle;
    (boundaryCollarDiffeomorph A p).val = q.val →
      collarMap A hR p = handleMap A hR ((boundaryHandleDiffeomorph A).symm q) := by
  let := boundaryPieceAtlas A .collar
  let := boundaryPieceAtlas A .handle
  intro he
  have hu : p.val.2.2 < -2 * (bump A).rOut := by
    apply (boundaryCollar_mem_handle_iff A p).mp
    rw [he]
    exact q.property
  have hpq : boundaryHandleDiffeomorph A (leftCollarToHandle A p hu) = q := by
    apply Subtype.ext
    have ht : (boundaryCollarDiffeomorph A p).val =
        (boundaryHandleDiffeomorph A (leftCollarToHandle A p hu)).val :=
      Subtype.ext (Subtype.ext (leftCollarToHandle_ambient A p hu))
    exact ht.symm.trans he
  have hi : (boundaryHandleDiffeomorph A).symm q = leftCollarToHandle A p hu := by
    rw [← hpq]
    exact (boundaryHandleDiffeomorph A).symm_apply_apply _
  rw [hi]
  exact left_overlap_agreement A hR p hu

theorem collar_exterior_agreement (p : boundaryCollarParameters A)
    (q : bottomCylinderBoundaryPart A) :
    letI := boundaryPieceAtlas A .collar; letI := boundaryPieceAtlas A .cylinder;
    (boundaryCollarDiffeomorph A p).val = q.val.val →
      collarMap A hR p = exteriorMap A hR ((exteriorBoundaryDiffeomorph A).symm q) := by
  let := boundaryPieceAtlas A .collar
  let := boundaryPieceAtlas A .cylinder
  intro he
  have hu : 2 * (bump A).rOut < p.val.2.2 := by
    apply (boundaryCollar_mem_cylinder_iff A p).mp
    rw [he]
    exact q.val.property
  have hpq : exteriorBoundaryDiffeomorph A (rightCollarToExterior A p hu) = q := by
    apply Subtype.ext
    apply Subtype.ext
    have ht : (boundaryCollarDiffeomorph A p).val =
        (exteriorBoundaryDiffeomorph A (rightCollarToExterior A p hu)).val.val :=
      Subtype.ext (Subtype.ext (rightCollarToExterior_ambient A p hu))
    exact ht.symm.trans he
  have hi : (exteriorBoundaryDiffeomorph A).symm q = rightCollarToExterior A p hu := by
    rw [← hpq]
    exact (exteriorBoundaryDiffeomorph A).symm_apply_apply _
  rw [hi]
  exact right_overlap_agreement A hR p hu

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
