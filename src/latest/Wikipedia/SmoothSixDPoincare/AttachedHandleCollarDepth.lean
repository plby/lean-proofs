import Wikipedia.SmoothSixDPoincare.SmoothClosedFaceDeficit
import Wikipedia.SmoothSixDPoincare.InwardCollarDepth
import Wikipedia.SmoothSixDPoincare.AttachedHandleNewCollar
import Wikipedia.SmoothSixDPoincare.FaceAttachmentMaps

/-!
# A continuous collar depth on the actual attached body

The old-body function and the whole-handle radial function agree on the
original attaching face and therefore descend to the actual quotient.
Both original collar coordinates and every new-face collar parameter have
their exact depth; no openness of the assembled collar is assumed.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

variable {E F G H X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (PuncturedHandle.UnitSphere E) F X)
  [TopologicalSpace Y] (i : C(X, Y)) (C : InwardBoundaryCollar i)

def handleCollarDepth : C(WholeHandle E F, ℝ) :=
  ⟨fun z => min 1 (HandleCollarDepth.depth (‖z.1.val‖ - 1) (1 - ‖z.2.val‖)),
    continuous_const.min (HandleCollarDepth.continuous_depth.comp
      (((continuous_subtype_val.comp continuous_fst).norm.sub continuous_const).prodMk
        (continuous_const.sub (continuous_subtype_val.comp continuous_snd).norm)))⟩

def oldCollarDepth : C(Y, ℝ) :=
  C.bodyDepth A.normalDeficit (fun x => (A.normalDeficit_bounds x).1)

theorem collarDepth_face (u : wholeAttachingFace E F) :
    oldCollarDepth A i C (bodyFaceMap A i u) = handleCollarDepth u.val := by
  change C.bodyDepth A.normalDeficit (fun x => (A.normalDeficit_bounds x).1)
      (i (A.map (wholeFaceCoordinates E F u))) =
    min 1 (HandleCollarDepth.depth (‖u.val.1.val‖ - 1) (1 - ‖u.val.2.val‖))
  rw [C.bodyDepth_boundary, A.normalDeficit_face, u.property, sub_self]
  rfl

def attachedCollarDepth : C(AttachedBody A i, ℝ) :=
  FaceAttachment.desc (bodyFaceMap A i) (oldCollarDepth A i C) handleCollarDepth
    (collarDepth_face A i C)

theorem attachedCollarDepth_old (y : Y) :
    attachedCollarDepth A i C (FaceAttachment.oldMap (bodyFaceMap A i) y) =
      oldCollarDepth A i C y := rfl

theorem attachedCollarDepth_handle (z : WholeHandle E F) :
    attachedCollarDepth A i C (FaceAttachment.handleMap (bodyFaceMap A i) z) =
      min 1 (HandleCollarDepth.depth (‖z.1.val‖ - 1) (1 - ‖z.2.val‖)) := rfl

theorem attachedCollarDepth_old_collar (q : X × unitInterval) :
    attachedCollarDepth A i C (FaceAttachment.oldMap (bodyFaceMap A i) (C.map q)) =
      min 1 (HandleCollarDepth.depth (q.2 : ℝ) (A.normalDeficit q.1)) :=
  C.bodyDepth_map A.normalDeficit (fun x => (A.normalDeficit_bounds x).1) q

theorem attachedCollarDepth_exterior (x : X) (hx : x ∉ A.interiorImage) (t : unitInterval) :
    attachedCollarDepth A i C (FaceAttachment.oldMap (bodyFaceMap A i) (C.map (x, t))) =
      (t : ℝ) := by
  rw [attachedCollarDepth_old_collar, A.normalDeficit_exterior x hx,
    HandleCollarDepth.depth_zero_deficit, max_eq_left t.property.1, min_eq_right t.property.2]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] (hi : Injective i)

theorem attachedCollarDepth_parametrization (z : WholeHandle E F) :
    attachedCollarDepth A i C
      (CollaredHandleEmbedding.parametrization A.map i C hi A.closedEmbedding.injective z) =
        min 1 (HandleCollarDepth.depth (2 * ‖z.1.val‖ - 1) (1 - ‖z.2.val‖)) := by
  obtain ⟨q, rfl⟩ := (CollaredDiskAttachment.homeomorph (E := E) (F := F)).surjective z
  induction q using Quot.inductionOn with
  | _ q =>
      cases q with
      | inl a =>
          rw [CollaredDiskAttachment.homeomorph_inl, CollaredHandleEmbedding.parametrization_old]
          change attachedCollarDepth A i C
              (FaceAttachment.oldMap (bodyFaceMap A i) (C.map (A.map (a.1, a.2.2), a.2.1))) = _
          rw [attachedCollarDepth_old_collar, A.normalDeficit_face]
          change min 1 (HandleCollarDepth.depth (a.2.1 : ℝ) (1 - ‖a.2.2.val‖)) =
            min 1 (HandleCollarDepth.depth
              (2 * ‖(CollaredDiskAttachment.collarPoint a.1 a.2.1).val‖ - 1) (1 - ‖a.2.2.val‖))
          rw [CollaredDiskAttachment.norm_collarPoint]
          have ht : 2 * CollaredDiskAttachment.collarRadius a.2.1 - 1 = (a.2.1 : ℝ) := by
            unfold CollaredDiskAttachment.collarRadius
            ring
          rw [ht]
      | inr z =>
          rw [CollaredDiskAttachment.homeomorph_inr, CollaredHandleEmbedding.parametrization_new]
          change attachedCollarDepth A i C (FaceAttachment.handleMap (bodyFaceMap A i) z) = _
          rw [attachedCollarDepth_handle]
          change min 1 (HandleCollarDepth.depth (‖z.1.val‖ - 1) (1 - ‖z.2.val‖)) =
            min 1 (HandleCollarDepth.depth
              (2 * ‖(CollaredDiskAttachment.halfPoint z.1).val‖ - 1) (1 - ‖z.2.val‖))
          rw [CollaredDiskAttachment.norm_halfPoint]
          congr 2
          ring

theorem attachedCollarDepth_new_collar (q : (MorseHandle.UnitDisk E ×
    PuncturedHandle.UnitSphere F) × unitInterval) :
    attachedCollarDepth A i C
      (CollaredHandleEmbedding.newCollarMap A.map i C hi A.closedEmbedding.injective q) =
        HandleCollarCoordinates.time q.2 := by
  change attachedCollarDepth A i C
    (CollaredHandleEmbedding.parametrization A.map i C hi A.closedEmbedding.injective
      (HandleCollarCoordinates.coordinates q)) = _
  rw [attachedCollarDepth_parametrization, HandleCollarCoordinates.depth_coordinates]
  exact min_eq_right ((HandleCollarCoordinates.time_le_half q.2).trans (by norm_num))

end Wikipedia.SmoothSixDPoincare.FramedSurgery
