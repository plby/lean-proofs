import Wikipedia.SmoothSixDPoincare.FaceAttachmentCompact
import Wikipedia.SmoothSixDPoincare.FramedSurgeryClosedPresentation

/-!
# Attach the whole handle through the given embedded old boundary

The attaching face and the new closed face retain the original product
coordinates. The body is the actual face-attachment quotient, not a new
Hausdorff replacement or a separately assumed realization.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

section Coordinates

variable (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F]

abbrev WholeHandle := MorseHandle.UnitDisk E × MorseHandle.UnitDisk F

def wholeAttachingFace : Set (WholeHandle E F) := {p | ‖p.1.val‖ = 1}

theorem isClosed_wholeAttachingFace : IsClosed (wholeAttachingFace E F) :=
  isClosed_eq (continuous_norm.comp (continuous_subtype_val.comp continuous_fst)) continuous_const

def wholeFaceCoordinates : wholeAttachingFace E F ≃ₜ
    (UnitSphere E × MorseHandle.UnitDisk F) where
  toFun p := (⟨p.val.1.val, mem_sphere_zero_iff_norm.mpr p.property⟩, p.val.2)
  invFun p := ⟨(⟨p.1.val, sphere_subset_closedBall p.1.property⟩, p.2),
    mem_sphere_zero_iff_norm.mp p.1.property⟩
  left_inv _p := rfl
  right_inv _p := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk
      continuous_snd).subtype_mk _

def wholeNewFace : C(ClosedNewFace E F, WholeHandle E F) :=
  ⟨fun p => (p.1, ⟨p.2.val, sphere_subset_closedBall p.2.property⟩),
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩

theorem wholeNewFace_injective : Injective (wholeNewFace E F) := by
  intro p q h
  refine Prod.ext (congrArg (fun z : WholeHandle E F => z.1) h) (Subtype.ext ?_)
  exact congrArg (fun z : WholeHandle E F => z.2.val) h

end Coordinates

variable {E F G H X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  (i : C(X, Y))

def bodyFaceMap : C(wholeAttachingFace E F, Y) :=
  i.comp (A.map.comp ⟨wholeFaceCoordinates E F, (wholeFaceCoordinates E F).continuous⟩)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space Y] [CompactSpace Y] in
theorem bodyFaceMap_injective (hi : Injective i) : Injective (bodyFaceMap A i) :=
  hi.comp (A.closedEmbedding.injective.comp (wholeFaceCoordinates E F).injective)

abbrev AttachedBody := FaceAttachment.Space (bodyFaceMap A i)

theorem attachedBodyT2Space (hi : Injective i) : T2Space (AttachedBody A i) :=
  FaceAttachment.t2Space (bodyFaceMap A i) (isClosed_wholeAttachingFace E F)
    (bodyFaceMap_injective A i hi)

def bodyExteriorMap : C(Exterior A, AttachedBody A i) :=
  (FaceAttachment.oldMap (bodyFaceMap A i)).comp (i.comp (exteriorOldMap A))

def bodyNewFaceMap : C(ClosedNewFace E F, AttachedBody A i) :=
  (FaceAttachment.handleMap (bodyFaceMap A i)).comp (wholeNewFace E F)

theorem bodyExteriorMap_isClosedEmbedding (hi : IsClosedEmbedding i) :
    IsClosedEmbedding (bodyExteriorMap A i) :=
  (FaceAttachment.oldMap_isClosedEmbedding (bodyFaceMap A i) (isClosed_wholeAttachingFace E F)
    (bodyFaceMap_injective A i hi.injective)).comp
      (hi.comp (exteriorOldMap_isClosedEmbedding A))

theorem bodyNewFaceMap_isClosedEmbedding (hi : Injective i) :
    IsClosedEmbedding (bodyNewFaceMap A i) := by
  let _ : T2Space (AttachedBody A i) := attachedBodyT2Space A i hi
  apply (bodyNewFaceMap A i).continuous.isClosedEmbedding
  exact (fun p q h => (wholeNewFace_injective E F)
    ((FaceAttachment.handleMap_eq_handleMap (bodyFaceMap A i)
      (bodyFaceMap_injective A i hi) _ _).mp h))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space Y] [CompactSpace Y] in
theorem bodyExteriorMap_corner (q : UnitSphere E × UnitSphere F) :
    bodyExteriorMap A i (exteriorCorner A q) =
      bodyNewFaceMap A i (⟨q.1.val, sphere_subset_closedBall q.1.property⟩, q.2) :=
  FaceAttachment.face_identification (bodyFaceMap A i)
    ((wholeFaceCoordinates E F).symm
      (q.1, ⟨q.2.val, sphere_subset_closedBall q.2.property⟩))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space Y] [CompactSpace Y] in
theorem bodyExteriorMap_eq_newFace (hi : Injective i) (r : Exterior A)
    (p : ClosedNewFace E F) :
    bodyExteriorMap A i r = bodyNewFaceMap A i p ↔
      ∃ q : UnitSphere E × UnitSphere F, r = exteriorCorner A q ∧
        p = (⟨q.1.val, sphere_subset_closedBall q.1.property⟩, q.2) := by
  constructor
  · intro h
    obtain ⟨u, hu, hup⟩ :=
      (FaceAttachment.oldMap_eq_handleMap (bodyFaceMap A i)
        (bodyFaceMap_injective A i hi) _ _).mp h
    have hr : A.map (wholeFaceCoordinates E F u) = exteriorOldMap A r := hi hu
    obtain ⟨q, hrq, huq⟩ :=
      (exterior_old_face_overlap A r (wholeFaceCoordinates E F u)).mp hr.symm
    refine ⟨q, hrq, ?_⟩
    have hu' := congrArg (fun z => ((wholeFaceCoordinates E F).symm z).val) huq
    rw [Homeomorph.symm_apply_apply] at hu'
    have he : wholeNewFace E F p =
        (⟨q.1.val, sphere_subset_closedBall q.1.property⟩,
          ⟨q.2.val, sphere_subset_closedBall q.2.property⟩) := hup.symm.trans hu'
    exact wholeNewFace_injective E F he
  · rintro ⟨q, rfl, rfl⟩
    exact bodyExteriorMap_corner A i q

end Wikipedia.SmoothSixDPoincare.FramedSurgery
