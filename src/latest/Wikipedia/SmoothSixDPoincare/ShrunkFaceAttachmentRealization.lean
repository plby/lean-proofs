import Wikipedia.SmoothSixDPoincare.MorseFaceAttachment
import Wikipedia.SmoothSixDPoincare.ShrunkMorseSurgery

/-!
# The actual first face quotient under its retained shrunk realization

Only the whole-sublevel realization changes. The original old-sublevel
face map and every coordinate of the original handle remain the same.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.ShrunkSurgeryRealization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} {d : MorseSurgeryData E f p} {s : ℝ}
  (R : d.ShrunkSurgeryRealization s)

open Classical in
def faceQuotientRealization (hf : Continuous f) :
    FaceAttachment.Space d.handleFaceToSublevel ≃ₜ
      {y : M // f y ≤ f p + d.radius ^ 2} :=
  (d.faceAttachmentRealization hf).trans (d.attachmentHomeomorph.symm.trans R.attachmentHomeomorph)

open Classical in
theorem faceQuotientRealization_old (hf : Continuous f)
    (x : {y : M // f y ≤ f p - d.radius ^ 2}) :
    R.faceQuotientRealization hf (FaceAttachment.oldMap d.handleFaceToSublevel x) =
      R.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩ := by
  change R.attachmentHomeomorph (d.attachmentHomeomorph.symm
    (d.faceAttachmentRealization hf (FaceAttachment.oldMap d.handleFaceToSublevel x))) = _
  rw [d.faceAttachmentRealization_old, Homeomorph.symm_apply_apply]

open Classical in
theorem faceQuotientRealization_handle (hf : Continuous f) (z : d.HandleDomain) :
    R.faceQuotientRealization hf (FaceAttachment.handleMap d.handleFaceToSublevel z) =
      R.attachmentHomeomorph ⟨d.handleMap z, Or.inr ⟨z, rfl⟩⟩ := by
  change R.attachmentHomeomorph (d.attachmentHomeomorph.symm
    (d.faceAttachmentRealization hf (FaceAttachment.handleMap d.handleFaceToSublevel z))) = _
  rw [d.faceAttachmentRealization_handle, Homeomorph.symm_apply_apply]

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.ShrunkSurgeryRealization
