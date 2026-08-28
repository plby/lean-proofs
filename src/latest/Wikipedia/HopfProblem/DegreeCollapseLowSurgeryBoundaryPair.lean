import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryNewCover
import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

/-!

# The constructed surgery boundary pair for the actual native new end

All closed embeddings, both exhaustive covers and both exact common-face
incidences are proved for the original manifold and native complementary
end. Radius normalization is constructed, so no radius hypothesis is needed
to obtain the normalized pair. Its attaching sphere is the original map.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace
open Wikipedia.SmoothSixDPoincare PuncturedHandle

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

def boundaryPair (hR : A.radius = 2) :
    SurgeryBoundaryPair (Vector (d + 1)) (Vector (7 - d)) (closedExterior A)
      M (otherBoundaryPart A) where
  oldExterior := oldExterior A
  newExterior := newExterior A
  oldPiece := oldPiece A
  newPiece := nativeCapPoint A hR
  oldExterior_closed := isClosedEmbedding_oldExterior A
  newExterior_closed := isClosedEmbedding_newExterior A
  oldPiece_closed := isClosedEmbedding_oldPiece A
  newPiece_closed := isClosedEmbedding_nativeCapPoint A hR
  old_cover := old_cover A
  new_cover := new_cover A hR
  boundary := commonFace A
  old_overlap := old_overlap A
  new_overlap := new_overlap A hR

theorem boundaryPair_attaching (hR : A.radius = 2) (s : NoExoticSixSphere.Sphere d) :
    (boundaryPair A hR).attachingSphere s = f s := by
  change A.tube (s, oldRadius A • (0 : Vector (7 - d))) = f s
  rw [smul_zero, A.tube_core]

theorem boundaryPair_belt_ambient (hR : A.radius = 2)
    (w : sphere (0 : Vector (7 - d)) 1) :
    ((boundaryPair A hR).beltSphere w).val.val.val = A.map (0, w.val) := by
  have hp : ‖capDisk A (ballZero, w)‖ ≤ cutRadius A := by
    change ‖oldRadius A • (0 : Vector (d + 1))‖ ≤ cutRadius A
    rw [smul_zero, norm_zero]
    exact (cutRadius_pos A).le
  change (nativeCapPoint A hR (ballZero, w)).val.val.val = _
  rw [nativeCapPoint_ambient, capPoint_of_inner A _ hp]
  change A.map (oldRadius A • (0 : Vector (d + 1)), w.val) = _
  rw [smul_zero]

def normalizedBoundaryPair :
    SurgeryBoundaryPair (Vector (d + 1)) (Vector (7 - d)) (closedExterior A.normalizedRadius)
      M (otherBoundaryPart A.normalizedRadius) :=
  boundaryPair A.normalizedRadius A.normalizedRadius_radius

theorem normalizedBoundaryPair_attaching (s : NoExoticSixSphere.Sphere d) :
    (normalizedBoundaryPair A).attachingSphere s = f s :=
  boundaryPair_attaching A.normalizedRadius A.normalizedRadius_radius s

theorem normalizedBoundaryPair_belt_ambient (w : sphere (0 : Vector (7 - d)) 1) :
    ((normalizedBoundaryPair A).beltSphere w).val.val.val =
      A.map (0, (A.radius / 2) • w.val) :=
  boundaryPair_belt_ambient A.normalizedRadius A.normalizedRadius_radius w

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
