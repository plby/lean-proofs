import Wikipedia.SmoothSixDPoincare.FaceAttachmentBoundaryUpdate
import Wikipedia.SmoothSixDPoincare.CommonBaseAttachmentRealization

/-! # Boundary updates retain exact changes of the face map and old-body coordinates -/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

variable {K X Y : Type*} [TopologicalSpace K] [TopologicalSpace X] [TopologicalSpace Y]
  {B : Set K} {b c : C(B, X)}

theorem congrFaceMap_updateBoundary (h : b = c) (S U : Set X) (V : Set K) :
    congrFaceMap h '' updateBoundary b S U V = updateBoundary c S U V := by
  subst c
  change id '' updateBoundary b S U V = _
  exact image_id _

theorem baseCongr_updateBoundary (b : C(B, X)) (e : X ≃ₜ Y)
    (S U : Set X) (V : Set K) :
    baseCongr b e '' updateBoundary b S U V =
      updateBoundary (e.toHomotopyEquiv.toFun.comp b) (e '' S) (e '' U) V := by
  unfold updateBoundary
  rw [image_union, image_image, image_image, ← image_sdiff e.injective, image_image]
  rfl

end Wikipedia.SmoothSixDPoincare.FaceAttachment
