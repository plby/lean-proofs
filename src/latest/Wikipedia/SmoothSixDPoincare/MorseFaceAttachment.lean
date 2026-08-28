import Wikipedia.SmoothSixDPoincare.FaceAttachmentRealization
import Wikipedia.SmoothSixDPoincare.TransportedMorseAttachment

/-!
# The original Morse attachment as a quotient of its actual face map

The face map lands in the actual lower sublevel and on its original level.
The quotient realization is the previously constructed whole attachment,
with both the entire old-sublevel map and all handle coordinates retained.
-/

noncomputable section

open Set Metric ContinuousMap Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def handleFaceToSublevel : C(d.handleFace, {y : M // f y ≤ f p - d.radius ^ 2}) :=
  ClosedAttachment.faceMap {y : M | f y ≤ f p - d.radius ^ 2} d.handleFace d.handleMap
    (fun z hz => (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block z).mpr hz)

open Classical in
theorem handleFaceToSublevel_coe (z : d.handleFace) :
    (d.handleFaceToSublevel z).val = d.handleMap z.val := rfl

open Classical in
theorem handleFaceToSublevel_level (z : d.handleFace) :
    f (d.handleFaceToSublevel z) = f p - d.radius ^ 2 :=
  d.chart.attachingHandleMap_boundary_height d.radius d.radius_pos d.block z.val z.property

open Classical in
theorem isClosed_handleFace : IsClosed d.handleFace := by
  change IsClosed {z : d.HandleDomain | ‖z.1.val‖ = 1}
  exact isClosed_eq (by fun_prop) continuous_const

open Classical in
theorem handleFaceToSublevel_isClosedEmbedding [T2Space M] :
    IsClosedEmbedding d.handleFaceToSublevel :=
  ClosedCover.isClosedEmbedding_codRestrict
    ((d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block).comp
      d.isClosed_handleFace.isClosedEmbedding_subtypeVal)
    (fun z => (d.handleFaceToSublevel z).property)

variable [T2Space M] [CompactSpace M]

open Classical in
def faceAttachmentRealization (hf : Continuous f) :
    FaceAttachment.Space d.handleFaceToSublevel ≃ₜ
      {y : M // f y ≤ f p + d.radius ^ 2} :=
  (ClosedAttachment.faceQuotientHomeomorph {y : M | f y ≤ f p - d.radius ^ 2}
    d.handleFace d.handleMap
      (fun z hz =>
        (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block z).mpr hz)).trans
          (d.attachmentQuotientHomeomorph hf)

open Classical in
theorem faceAttachmentRealization_old (hf : Continuous f)
    (x : {y : M // f y ≤ f p - d.radius ^ 2}) :
    d.faceAttachmentRealization hf (FaceAttachment.oldMap d.handleFaceToSublevel x) =
      d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩ := rfl

open Classical in
theorem faceAttachmentRealization_handle (hf : Continuous f) (z : d.HandleDomain) :
    d.faceAttachmentRealization hf (FaceAttachment.handleMap d.handleFaceToSublevel z) =
      d.attachmentHomeomorph ⟨d.handleMap z, Or.inr ⟨z, rfl⟩⟩ := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
