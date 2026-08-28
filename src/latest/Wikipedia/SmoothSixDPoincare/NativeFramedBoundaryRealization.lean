import Wikipedia.SmoothSixDPoincare.NativeFramedAttachingFace
import Wikipedia.SmoothSixDPoincare.FramedSurgeryPresentationComparison
import Wikipedia.SmoothSixDPoincare.CommonBaseAttachmentRealization

/-!
# Realize the constructed framed boundary in the original native upper sublevel

Both the whole-body quotient and its designated boundary use the original
native attaching map. The recorded native surgery presentation identifies
the constructed boundary with the actual upper level. The two realizations
agree pointwise after inclusion into the actual upper sublevel.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]

open Classical in
def framedBodyRealization :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.AttachedBody (d.attachingSmoothFace hf m) d.lowerBodyInclusion ≃ₜ
      {x : M // f x ≤ f p + d.radius ^ 2} := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  exact (FaceAttachment.congrFaceMap (d.attachingSmoothFace_bodyFace hf m)).trans
    (d.faceAttachmentRealization hf.continuous)

open Classical in
theorem framedBodyRealization_old (x : {x : M // f x ≤ f p - d.radius ^ 2}) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    d.framedBodyRealization hf m
      (FaceAttachment.oldMap (FramedSurgery.bodyFaceMap
        (d.attachingSmoothFace hf m) d.lowerBodyInclusion) x) =
      d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  change d.faceAttachmentRealization hf.continuous
    (FaceAttachment.congrFaceMap (d.attachingSmoothFace_bodyFace hf m)
      (FaceAttachment.oldMap _ x)) = _
  exact (congrArg (d.faceAttachmentRealization hf.continuous)
    (FaceAttachment.congrFaceMap_old (d.attachingSmoothFace_bodyFace hf m) x)).trans
      (d.faceAttachmentRealization_old hf.continuous x)

open Classical in
theorem framedBodyRealization_handle (z : d.HandleDomain) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    d.framedBodyRealization hf m
      (FaceAttachment.handleMap (FramedSurgery.bodyFaceMap
        (d.attachingSmoothFace hf m) d.lowerBodyInclusion) z) =
      d.attachmentHomeomorph ⟨d.handleMap z, Or.inr ⟨z, rfl⟩⟩ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  change d.faceAttachmentRealization hf.continuous
    (FaceAttachment.congrFaceMap (d.attachingSmoothFace_bodyFace hf m)
      (FaceAttachment.handleMap _ z)) = _
  exact (congrArg (d.faceAttachmentRealization hf.continuous)
    (FaceAttachment.congrFaceMap_handle (d.attachingSmoothFace_bodyFace hf m) z)).trans
      (d.faceAttachmentRealization_handle hf.continuous z)

open Classical in
omit [CompactSpace M] in
theorem attachingSmoothFace_oldPiece :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z, d.surgery.oldPiece z = (d.attachingSmoothFace hf m).map
      (FramedSurgery.oldFaceCoordinates
        d.chart.NegativeCoordinates d.chart.PositiveCoordinates z) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro z
  exact (d.attachingFace_oldPiece
    (FramedSurgery.oldFaceCoordinates
      d.chart.NegativeCoordinates d.chart.PositiveCoordinates z)).symm

variable (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]

open Classical in
abbrev FramedBoundary :=
  letI := RegularLevel.chartedSpace hf d.lower_regular
  FramedSurgery.Boundary (d.attachingSmoothFace hf m) n

open Classical in
omit [CompactSpace M] in
theorem nonempty_framedSmoothBoundaryData :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    Nonempty (FramedSurgery.SmoothBoundaryData (d.attachingSmoothFace hf m) n) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.isManifold hf d.lower_regular
  exact FramedSurgery.nonempty_smoothBoundaryData (d.attachingSmoothFace hf m) n

open Classical in
def framedBoundaryRealization : d.FramedBoundary hf m n ≃ₜ d.UpperLevel := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  exact FramedSurgery.presentationBoundaryHomeomorph (d.attachingSmoothFace hf m) d.surgery
    (d.attachingSmoothFace_oldPiece hf m) n

open Classical in
def framedBoundaryBodyMap : C(d.FramedBoundary hf m n,
    {x : M // f x ≤ f p + d.radius ^ 2}) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  exact ⟨fun z => d.framedBodyRealization hf m
      (FramedSurgery.boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
        (d.lowerBodyInclusion_isClosedEmbedding hf) z),
    (d.framedBodyRealization hf m).continuous.comp
      (FramedSurgery.boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
        (d.lowerBodyInclusion_isClosedEmbedding hf)).continuous⟩

open Classical in
theorem framedBoundaryBodyMap_isClosedEmbedding :
    IsClosedEmbedding (d.framedBoundaryBodyMap hf m n) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  exact (d.framedBodyRealization hf m).isClosedEmbedding.comp
    (FramedSurgery.boundaryBodyMap_isClosedEmbedding (d.attachingSmoothFace hf m)
      d.lowerBodyInclusion n (d.lowerBodyInclusion_isClosedEmbedding hf))

open Classical in
theorem framedBoundary_realizations_agree (z : d.FramedBoundary hf m n) :
    (d.framedBoundaryBodyMap hf m n z).val = (d.framedBoundaryRealization hf m n z).val := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  let A := d.attachingSmoothFace hf m
  have hz : z ∈ range (FramedSurgery.exteriorNewMap A n) ∪
      range (FramedSurgery.closedNewMap A n) := by
    rw [FramedSurgery.exterior_new_face_cover A n]
    trivial
  rcases hz with ⟨r, rfl⟩ | ⟨q, rfl⟩
  · change (d.framedBodyRealization hf m
      (FramedSurgery.boundaryBodyMap A d.lowerBodyInclusion n
        (d.lowerBodyInclusion_isClosedEmbedding hf) (FramedSurgery.exteriorNewMap A n r))).val =
        (FramedSurgery.presentationBoundaryHomeomorph A d.surgery
          (d.attachingSmoothFace_oldPiece hf m) n (FramedSurgery.exteriorNewMap A n r)).val
    rw [FramedSurgery.boundaryBodyMap_exterior, d.framedBodyRealization_old,
      FramedSurgery.presentationBoundaryHomeomorph_exterior, d.newExterior_eq]
    apply congrArg (fun y => (d.attachmentHomeomorph y).val)
    apply Subtype.ext
    have he := FramedSurgery.presentationExteriorCoordinates_point A d.surgery
      (d.attachingSmoothFace_oldPiece hf m) r
    exact (congrArg (fun x : d.LowerLevel => x.val) he).symm.trans (d.oldExterior_eq _)
  · change (d.framedBodyRealization hf m
      (FramedSurgery.boundaryBodyMap A d.lowerBodyInclusion n
        (d.lowerBodyInclusion_isClosedEmbedding hf) (FramedSurgery.closedNewMap A n q))).val =
        (FramedSurgery.presentationBoundaryHomeomorph A d.surgery
          (d.attachingSmoothFace_oldPiece hf m) n (FramedSurgery.closedNewMap A n q)).val
    rw [FramedSurgery.boundaryBodyMap_newFace, d.framedBodyRealization_handle,
      FramedSurgery.presentationBoundaryHomeomorph_newFace, d.newPiece_eq]
    rfl

open Classical in
theorem framedBoundaryBodyMap_range : range (d.framedBoundaryBodyMap hf m n) =
    {x : {x : M // f x ≤ f p + d.radius ^ 2} | f x.val = f p + d.radius ^ 2} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change f (d.framedBoundaryBodyMap hf m n z).val = _
    rw [d.framedBoundary_realizations_agree hf m n]
    exact (d.framedBoundaryRealization hf m n z).property
  · intro hx
    let y : d.UpperLevel := ⟨x.val, hx⟩
    refine ⟨(d.framedBoundaryRealization hf m n).symm y, Subtype.ext ?_⟩
    rw [d.framedBoundary_realizations_agree hf m n, Homeomorph.apply_symm_apply]

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
