import Wikipedia.SmoothSixDPoincare.FaceAttachmentPieceCoordinates
import Wikipedia.SmoothSixDPoincare.MorseFaceAttachment
import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryReverse

/-!
# A top-index native Morse step is an actual full-boundary disk cap

The positive coordinate space is proved to be a subsingleton. Projection
identifies the whole handle with its negative disk and the original face
with that disk's entire boundary. The cap quotient realizes the original
upper sublevel with the original old and whole-handle maps.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
theorem subsingleton_positive_of_top_index
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E) :
    Subsingleton d.chart.PositiveCoordinates := by
  have h := d.chart.finrank_negative_add_positive
  have hz : Module.finrank ℝ d.chart.PositiveCoordinates = 0 := by omega
  exact Module.finrank_zero_iff.mp hz

open Classical in
def topIndexHandleCoordinates
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E) :
    d.HandleDomain ≃ₜ MorseHandle.UnitDisk d.chart.NegativeCoordinates := by
  let _ := d.subsingleton_positive_of_top_index hindex
  exact {
    toFun := Prod.fst
    invFun := fun u => (u, ⟨0, by simp⟩)
    left_inv := fun _ => Prod.ext rfl (Subsingleton.elim _ _)
    right_inv := fun _ => rfl
    continuous_toFun := continuous_fst
    continuous_invFun := continuous_id.prodMk continuous_const }

open Classical in
def capBoundary : Set (MorseHandle.UnitDisk d.chart.NegativeCoordinates) :=
  {u | ‖u.val‖ = 1}

open Classical in
def capFaceToSublevel : C(d.capBoundary, {y : M // f y ≤ f p - d.radius ^ 2}) :=
  d.handleFaceToSublevel.comp ⟨fun u => ⟨(u.val, ⟨0, by simp⟩), u.property⟩,
    (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩

open Classical in
theorem capFaceToSublevel_attaching
    (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    (d.capFaceToSublevel
      ⟨⟨u.val, sphere_subset_closedBall u.property⟩, mem_sphere_zero_iff_norm.mp u.property⟩).val =
      (d.surgery.attachingSphere u).val :=
  d.handleMap_core u

open Classical in
theorem topIndexHandleCoordinates_face
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E)
    (z : d.HandleDomain) :
    d.topIndexHandleCoordinates hindex z ∈ d.capBoundary ↔ z ∈ d.handleFace := Iff.rfl

open Classical in
theorem topIndexHandleCoordinates_faceMap
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E)
    (u : d.handleFace) :
    d.capFaceToSublevel ⟨d.topIndexHandleCoordinates hindex u.val,
      (d.topIndexHandleCoordinates_face hindex u.val).mpr u.property⟩ =
      d.handleFaceToSublevel u := by
  let _ := d.subsingleton_positive_of_top_index hindex
  apply congrArg d.handleFaceToSublevel
  apply Subtype.ext
  exact Prod.ext rfl (Subsingleton.elim _ _)

open Classical in
def topIndexBoundaryHomeomorph
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E) :
    (d.UpperLevel ⊕ PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) ≃ₜ d.LowerLevel := by
  let _ := d.subsingleton_positive_of_top_index hindex
  exact d.surgery.topIndexBoundaryHomeomorph

open Classical in
theorem topIndexBoundaryHomeomorph_attaching
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E)
    (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    d.topIndexBoundaryHomeomorph hindex (Sum.inr u) = d.surgery.attachingSphere u := rfl

variable [T2Space M] [CompactSpace M]

open Classical in
def topIndexCapRealization (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E) :
    FaceAttachment.Space d.capFaceToSublevel ≃ₜ {y : M // f y ≤ f p + d.radius ^ 2} :=
  (FaceAttachment.pieceCoordinates d.handleFaceToSublevel d.capFaceToSublevel
    (d.topIndexHandleCoordinates hindex) (d.topIndexHandleCoordinates_face hindex)
    (d.topIndexHandleCoordinates_faceMap hindex)).symm.trans (d.faceAttachmentRealization hf)

open Classical in
theorem topIndexCapRealization_old (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E)
    (x : {y : M // f y ≤ f p - d.radius ^ 2}) :
    d.topIndexCapRealization hf hindex (FaceAttachment.oldMap d.capFaceToSublevel x) =
      d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩ := rfl

open Classical in
theorem topIndexCapRealization_disk (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E)
    (u : MorseHandle.UnitDisk d.chart.NegativeCoordinates) :
    d.topIndexCapRealization hf hindex (FaceAttachment.handleMap d.capFaceToSublevel u) =
      d.attachmentHomeomorph ⟨d.handleMap (u, ⟨0, by simp⟩), Or.inr ⟨_, rfl⟩⟩ := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
