import Wikipedia.SmoothSixDPoincare.MorseFaceAttachment
import Wikipedia.SmoothSixDPoincare.FaceAttachmentHandleChange
import Wikipedia.SmoothSixDPoincare.FramedSurgeryDiskChange
import Wikipedia.SmoothSixDPoincare.MorseBeltFaceCoordinates

/-!
# The explicit belt correction on the original native whole-handle quotient

This is the same sphere-fixed negative-disk change, expressed directly on
the original native handle and its prescribed face quotient. It fixes the
old body and retains the exact reparametrization on every handle point.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def beltHandleChange : d.HandleDomain ≃ₜ d.HandleDomain :=
  FramedSurgery.wholeHandleDiskChange MorseHandle.beltFaceDiskHomeomorph

open Classical in
theorem beltHandleChange_face (z : d.HandleDomain) (hz : z ∈ d.handleFace) :
    d.beltHandleChange z = z :=
  FramedSurgery.wholeHandleDiskChange_face MorseHandle.beltFaceDiskHomeomorph
    MorseHandle.beltFaceDiskHomeomorph_boundary z hz

open Classical in
def beltFaceQuotientChange :
    FaceAttachment.Space d.handleFaceToSublevel ≃ₜ FaceAttachment.Space d.handleFaceToSublevel :=
  FaceAttachment.handleChange d.handleFaceToSublevel d.beltHandleChange d.beltHandleChange_face

open Classical in
theorem beltFaceQuotientChange_old (x : {x : M // f x ≤ f p - d.radius ^ 2}) :
    d.beltFaceQuotientChange (FaceAttachment.oldMap d.handleFaceToSublevel x) =
      FaceAttachment.oldMap d.handleFaceToSublevel x := rfl

open Classical in
theorem beltFaceQuotientChange_handle (z : d.HandleDomain) :
    d.beltFaceQuotientChange (FaceAttachment.handleMap d.handleFaceToSublevel z) =
      FaceAttachment.handleMap d.handleFaceToSublevel (d.beltHandleChange z) := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
