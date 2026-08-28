import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
import Wikipedia.SmoothSixDPoincare.FramedSurgeryBodyAttachment
import Wikipedia.SmoothSixDPoincare.NativeMorseBoundaryPair

/-!
# A common whole-handle attachment for the actual surgery pair

Attach the full product disk to the original old space along its given
closed old piece. The quotient topology is compact Hausdorff, and its old
space and whole handle are closed embedded. All face coordinates are the
original ones from the surgery pair. No smooth cobordism is assumed here.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody

open Wikipedia.SmoothSixDPoincare PuncturedHandle MorseHandle

variable {E F R X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace R] [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] (d : SurgeryBoundaryPair E F R X Y)

def faceCoordinates : FramedSurgery.wholeAttachingFace E F ≃ₜ
    UnitSphere E × UnitBall F :=
  (FramedSurgery.wholeFaceCoordinates E F).trans
    ((Homeomorph.refl (UnitSphere E)).prodCongr (unitBallHomeomorph F).symm)

def faceMap : C(FramedSurgery.wholeAttachingFace E F, X) :=
  ⟨d.oldPiece ∘ faceCoordinates (E := E) (F := F),
    d.oldPiece_closed.continuous.comp (faceCoordinates (E := E) (F := F)).continuous⟩

theorem faceMap_injective : Injective (faceMap d) :=
  d.oldPiece_closed.injective.comp (faceCoordinates (E := E) (F := F)).injective

abbrev Space := FaceAttachment.Space (faceMap d)

instance t2Space : T2Space (Space d) :=
  FaceAttachment.t2Space (faceMap d) (FramedSurgery.isClosed_wholeAttachingFace E F)
    (faceMap_injective d)

def oldMap : C(X, Space d) := FaceAttachment.oldMap (faceMap d)

def handleMap : C(UnitDisk E × UnitDisk F, Space d) :=
  FaceAttachment.handleMap (faceMap d)

theorem oldMap_closed : IsClosedEmbedding (oldMap d) :=
  FaceAttachment.oldMap_isClosedEmbedding (faceMap d)
    (FramedSurgery.isClosed_wholeAttachingFace E F) (faceMap_injective d)

theorem handleMap_closed : IsClosedEmbedding (handleMap d) :=
  FaceAttachment.handleMap_isClosedEmbedding (faceMap d)
    (FramedSurgery.isClosed_wholeAttachingFace E F) (faceMap_injective d)

theorem old_cover : range (oldMap d) ∪ range (handleMap d) = univ :=
  eq_univ_of_forall (FaceAttachment.cover (faceMap d))

theorem oldMap_eq_handleMap (x : X) (z : UnitDisk E × UnitDisk F) :
    oldMap d x = handleMap d z ↔
      ∃ u : FramedSurgery.wholeAttachingFace E F, faceMap d u = x ∧ u.val = z :=
  FaceAttachment.oldMap_eq_handleMap (faceMap d) (faceMap_injective d) x z

theorem handle_mem_old_iff (z : UnitDisk E × UnitDisk F) :
    handleMap d z ∈ range (oldMap d) ↔ ‖z.1.val‖ = 1 := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨u, -, hu⟩ := (oldMap_eq_handleMap d x z).mp hx
    exact hu ▸ u.property
  · intro hz
    exact ⟨faceMap d ⟨z, hz⟩, FaceAttachment.face_identification (faceMap d) ⟨z, hz⟩⟩

def oldFace (p : UnitSphere E × UnitBall F) : UnitDisk E × UnitDisk F :=
  (⟨p.1.val, sphere_subset_closedBall p.1.property⟩, unitBallHomeomorph F p.2)

def newFace : C(UnitBall E × UnitSphere F, UnitDisk E × UnitDisk F) :=
  ⟨fun p ↦ (unitBallHomeomorph E p.1, ⟨p.2.val, sphere_subset_closedBall p.2.property⟩),
    ((unitBallHomeomorph E).continuous.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩

theorem newFace_injective : Injective (newFace (E := E) (F := F)) := by
  intro p q h
  refine Prod.ext ((unitBallHomeomorph E).injective (congrArg Prod.fst h)) ?_
  exact Subtype.ext (congrArg (fun z : UnitDisk E × UnitDisk F ↦ z.2.val) h)

theorem old_face_identification (p : UnitSphere E × UnitBall F) :
    oldMap d (d.oldPiece p) = handleMap d (oldFace p) :=
  FaceAttachment.face_identification (faceMap d)
    ⟨oldFace p, mem_sphere_zero_iff_norm.mp p.1.property⟩

def exteriorMap : C(R, Space d) :=
  (oldMap d).comp ⟨d.oldExterior, d.oldExterior_closed.continuous⟩

def newPieceMap : C(UnitBall E × UnitSphere F, Space d) :=
  (handleMap d).comp newFace

theorem exteriorMap_closed : IsClosedEmbedding (exteriorMap d) :=
  (oldMap_closed d).comp d.oldExterior_closed

theorem newPieceMap_closed : IsClosedEmbedding (newPieceMap d) := by
  let : CompactSpace (UnitBall E) := (unitBallHomeomorph E).symm.compactSpace
  exact (newPieceMap d).continuous.isClosedEmbedding
    ((handleMap_closed d).injective.comp newFace_injective)

theorem exterior_corner (q : UnitSphere E × UnitSphere F) :
    exteriorMap d (d.boundary q) = newPieceMap d (newBoundary q) := by
  change oldMap d (d.oldExterior (d.boundary q)) = handleMap d _
  rw [(d.old_overlap (d.boundary q) (oldBoundary q)).mpr ⟨q, rfl, rfl⟩]
  exact old_face_identification d (oldBoundary q)

theorem exterior_eq_newPiece (r : R) (p : UnitBall E × UnitSphere F) :
    exteriorMap d r = newPieceMap d p ↔
      ∃ q, r = d.boundary q ∧ p = newBoundary q := by
  constructor
  · intro h
    obtain ⟨u, hu, hup⟩ := (oldMap_eq_handleMap d (d.oldExterior r) (newFace p)).mp h
    obtain ⟨q, hr, hq⟩ := (d.old_overlap r (faceCoordinates u)).mp hu.symm
    refine ⟨q, hr, newFace_injective ?_⟩
    have he := congrArg (fun z ↦ ((faceCoordinates (E := E) (F := F)).symm z).val) hq
    rw [Homeomorph.symm_apply_apply] at he
    exact hup.symm.trans he
  · rintro ⟨q, rfl, rfl⟩
    exact exterior_corner d q

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody
