import Wikipedia.SmoothSixDPoincare.MorseFaceAttachment

/-!
# Transport the actual whole Morse attachment through a sublevel homeomorphism

Only the original face map changes. The constructed quotient still realizes
the same original upper sublevel, and every whole-handle coordinate has its
original image. If the base comparison preserves the native level, the new
face also lands on that level. No ambient extension or smoothness is assumed.
-/

noncomputable section

open Set ContinuousMap Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace X]
  {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (A : {y : M // f y ≤ f p - d.radius ^ 2} ≃ₜ X)

open Classical in
def transportedFaceMap : C(d.handleFace, X) :=
  A.toHomotopyEquiv.toFun.comp d.handleFaceToSublevel

open Classical in
theorem transportedFaceMap_apply (z : d.handleFace) :
    d.transportedFaceMap A z = A (d.handleFaceToSublevel z) := rfl

open Classical in
theorem transportedFaceMap_isClosedEmbedding [T2Space M] :
    IsClosedEmbedding (d.transportedFaceMap A) :=
  A.isClosedEmbedding.comp d.handleFaceToSublevel_isClosedEmbedding

variable [T2Space M] [CompactSpace M]

open Classical in
def transportedFaceRealization (hf : Continuous f) :
    FaceAttachment.Space (d.transportedFaceMap A) ≃ₜ
      {y : M // f y ≤ f p + d.radius ^ 2} :=
  FaceAttachment.changedRealization d.handleFaceToSublevel A (d.faceAttachmentRealization hf)

open Classical in
theorem transportedFaceRealization_old (hf : Continuous f) (x : X) :
    d.transportedFaceRealization A hf (FaceAttachment.oldMap (d.transportedFaceMap A) x) =
      d.attachmentHomeomorph ⟨(A.symm x).val, Or.inl (A.symm x).property⟩ :=
  (FaceAttachment.changedRealization_old d.handleFaceToSublevel A
    (d.faceAttachmentRealization hf) x).trans (d.faceAttachmentRealization_old hf (A.symm x))

open Classical in
theorem transportedFaceRealization_handle (hf : Continuous f) (z : d.HandleDomain) :
    d.transportedFaceRealization A hf (FaceAttachment.handleMap (d.transportedFaceMap A) z) =
      d.attachmentHomeomorph ⟨d.handleMap z, Or.inr ⟨z, rfl⟩⟩ :=
  (FaceAttachment.changedRealization_handle d.handleFaceToSublevel A
    (d.faceAttachmentRealization hf) z).trans (d.faceAttachmentRealization_handle hf z)

omit [T2Space M] [CompactSpace M] in
open Classical in
theorem transportedFaceMap_level {g : X → ℝ} {a : ℝ}
    (hA : ∀ x, g (A x) = a ↔ f x.val = f p - d.radius ^ 2) (z : d.handleFace) :
    g (d.transportedFaceMap A z) = a :=
  (hA (d.handleFaceToSublevel z)).mpr (d.handleFaceToSublevel_level z)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
