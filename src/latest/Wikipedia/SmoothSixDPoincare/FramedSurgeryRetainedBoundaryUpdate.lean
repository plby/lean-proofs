import Wikipedia.SmoothSixDPoincare.FramedSurgeryBoundaryUpdate
import Wikipedia.SmoothSixDPoincare.FramedSurgeryRetainedBodyFace
import Wikipedia.SmoothSixDPoincare.FaceAttachmentBoundaryChange

/-!
# The retained second face gives the literal second whole-body boundary update

The entire removed face interior and the original whole-handle attaching
map retain their exact old-body coordinates. Thus the second actual
attachment is the same iterated quotient used by whole-handle interchange.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery.SmoothBoundaryData

open PuncturedHandle

variable {E F G H X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  {A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X}
  {n : ℕ} [Fact (Module.finrank ℝ F = n + 1)] (P : SmoothBoundaryData A n)
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (i : C(X, Y)) (hi : IsClosedEmbedding i)

section GeneralFace

variable {D K B N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D K} [TopologicalSpace B] [ChartedSpace K B]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [CompactSpace (B × MorseHandle.UnitDisk N)]
  (C : SmoothClosedFace I J B N X) (hC : Disjoint (range C.map) (range A.map))

theorem retainClosedDisjointFace_interior_bodyImage :
    letI := P.charted
    boundaryBodyMap A i n hi '' (P.retainClosedDisjointFace C hC).interiorImage =
      (FaceAttachment.oldMap (bodyFaceMap A i) ∘ i) '' C.interiorImage := by
  let _ := P.charted
  unfold SmoothClosedFace.interiorImage
  rw [image_image, image_image]
  exact congrArg (fun h : B × MorseHandle.UnitDisk N → AttachedBody A i =>
    h '' ((univ : Set B) ×ˢ {v : MorseHandle.UnitDisk N | ‖v.val‖ < 1}))
      (funext (P.retainClosedDisjointFace_bodyMap i hi C hC))

end GeneralFace

variable {E₂ F₂ : Type*}
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {r : ℕ} [Fact (Module.finrank ℝ E₂ = r + 1)]
  (C : SmoothClosedFace (𝓡 r) J (UnitSphere E₂) F₂ X)
  (hC : Disjoint (range C.map) (range A.map))

theorem retainClosedDisjointFace_bodyFaceMap :
    letI := P.charted
    bodyFaceMap (P.retainClosedDisjointFace C hC) (boundaryBodyMap A i n hi) =
      (FaceAttachment.oldMap (bodyFaceMap A i)).comp (bodyFaceMap C i) := by
  let _ := P.charted
  ext u
  exact P.retainClosedDisjointFace_bodyMap i hi C hC (wholeFaceCoordinates E₂ F₂ u)

def retainedAttachmentCoordinates :
    letI := P.charted
    AttachedBody (P.retainClosedDisjointFace C hC) (boundaryBodyMap A i n hi) ≃ₜ
      FaceAttachment.Space ((FaceAttachment.oldMap (bodyFaceMap A i)).comp (bodyFaceMap C i)) := by
  let _ := P.charted
  exact FaceAttachment.congrFaceMap (P.retainClosedDisjointFace_bodyFaceMap i hi C hC)

theorem retainedAttachmentCoordinates_old (x : AttachedBody A i) :
    letI := P.charted
    P.retainedAttachmentCoordinates i hi C hC
      (FaceAttachment.oldMap
        (bodyFaceMap (P.retainClosedDisjointFace C hC) (boundaryBodyMap A i n hi)) x) =
      FaceAttachment.oldMap
        ((FaceAttachment.oldMap (bodyFaceMap A i)).comp (bodyFaceMap C i)) x := by
  let _ := P.charted
  exact FaceAttachment.congrFaceMap_old (P.retainClosedDisjointFace_bodyFaceMap i hi C hC) x

theorem retainedAttachmentCoordinates_handle (k : WholeHandle E₂ F₂) :
    letI := P.charted
    P.retainedAttachmentCoordinates i hi C hC
      (FaceAttachment.handleMap
        (bodyFaceMap (P.retainClosedDisjointFace C hC) (boundaryBodyMap A i n hi)) k) =
      FaceAttachment.handleMap
        ((FaceAttachment.oldMap (bodyFaceMap A i)).comp (bodyFaceMap C i)) k := by
  let _ := P.charted
  exact FaceAttachment.congrFaceMap_handle (P.retainClosedDisjointFace_bodyFaceMap i hi C hC) k

theorem retainedAttachmentCoordinates_boundary :
    letI := P.charted
    P.retainedAttachmentCoordinates i hi C hC ''
      bodyBoundarySet (P.retainClosedDisjointFace C hC) (boundaryBodyMap A i n hi) =
        FaceAttachment.updateBoundary
          ((FaceAttachment.oldMap (bodyFaceMap A i)).comp (bodyFaceMap C i))
          (bodyBoundarySet A i) ((FaceAttachment.oldMap (bodyFaceMap A i) ∘ i) '' C.interiorImage)
          (range (wholeNewFace E₂ F₂)) := by
  let _ := P.charted
  rw [bodyBoundarySet_eq_updateBoundary _ _ (boundaryBodyMap_isClosedEmbedding A i n hi).injective]
  change FaceAttachment.congrFaceMap (P.retainClosedDisjointFace_bodyFaceMap i hi C hC) '' _ = _
  rw [FaceAttachment.congrFaceMap_updateBoundary, boundaryBodyMap_range,
    P.retainClosedDisjointFace_interior_bodyImage i hi C hC]

end Wikipedia.SmoothSixDPoincare.FramedSurgery.SmoothBoundaryData
