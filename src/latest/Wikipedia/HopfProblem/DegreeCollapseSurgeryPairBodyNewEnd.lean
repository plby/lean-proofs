import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairBody
import Wikipedia.SmoothSixDPoincare.ClosedPieceMaps

/-!
# The actual new surgery space in the common attachment

The common exterior and the new closed face glue to a closed embedding of
the original new space. Its intersection with the whole handle is exactly
the opposite face. The same compact Hausdorff quotient therefore has both
whole-handle presentations, with no change to either endpoint topology.
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

theorem newPieces_agree (r : R) (p : UnitBall E × UnitSphere F)
    (h : d.newExterior r = d.newPiece p) : exteriorMap d r = newPieceMap d p :=
  (exterior_eq_newPiece d r p).mpr ((d.new_overlap r p).mp h)

def newMap : C(Y, Space d) :=
  ClosedCover.mapOfClosedPieces d.newExterior d.newPiece d.newExterior_closed
    d.newPiece_closed d.new_cover (exteriorMap d) (newPieceMap d) (newPieces_agree d)

theorem newMap_exterior (r : R) : newMap d (d.newExterior r) = exteriorMap d r :=
  ClosedCover.mapOfClosedPieces_left d.newExterior d.newPiece d.newExterior_closed
    d.newPiece_closed d.new_cover (exteriorMap d) (newPieceMap d) (newPieces_agree d) r

theorem newMap_piece (p : UnitBall E × UnitSphere F) :
    newMap d (d.newPiece p) = newPieceMap d p :=
  ClosedCover.mapOfClosedPieces_right d.newExterior d.newPiece d.newExterior_closed
    d.newPiece_closed d.new_cover (exteriorMap d) (newPieceMap d) (newPieces_agree d) p

theorem newMap_injective : Injective (newMap d) := by
  intro x y h
  have hx : x ∈ range d.newExterior ∪ range d.newPiece := by rw [d.new_cover]; trivial
  have hy : y ∈ range d.newExterior ∪ range d.newPiece := by rw [d.new_cover]; trivial
  rcases hx with ⟨r, rfl⟩ | ⟨p, rfl⟩
  · rcases hy with ⟨s, rfl⟩ | ⟨q, rfl⟩
    · rw [newMap_exterior, newMap_exterior] at h
      exact congrArg d.newExterior ((exteriorMap_closed d).injective h)
    · rw [newMap_exterior, newMap_piece] at h
      exact (d.new_overlap r q).mpr ((exterior_eq_newPiece d r q).mp h)
  · rcases hy with ⟨s, rfl⟩ | ⟨q, rfl⟩
    · rw [newMap_piece, newMap_exterior] at h
      exact ((d.new_overlap s p).mpr ((exterior_eq_newPiece d s p).mp h.symm)).symm
    · rw [newMap_piece, newMap_piece] at h
      exact congrArg d.newPiece ((newPieceMap_closed d).injective h)

theorem newMap_eq_handleMap (y : Y) (z : UnitDisk E × UnitDisk F) :
    newMap d y = handleMap d z ↔
      ∃ p : UnitBall E × UnitSphere F, d.newPiece p = y ∧ newFace p = z := by
  constructor
  · intro h
    have hy : y ∈ range d.newExterior ∪ range d.newPiece := by rw [d.new_cover]; trivial
    rcases hy with ⟨r, rfl⟩ | ⟨p, rfl⟩
    · rw [newMap_exterior] at h
      obtain ⟨u, hu, huz⟩ := (oldMap_eq_handleMap d (d.oldExterior r) z).mp h
      obtain ⟨q, hr, hp⟩ := (d.old_overlap r (faceCoordinates u)).mp hu.symm
      refine ⟨newBoundary q, ((d.new_overlap r (newBoundary q)).mpr ⟨q, hr, rfl⟩).symm, ?_⟩
      have he := congrArg (fun p ↦ ((faceCoordinates (E := E) (F := F)).symm p).val) hp
      rw [Homeomorph.symm_apply_apply] at he
      exact he.symm.trans huz
    · rw [newMap_piece] at h
      exact ⟨p, rfl, (handleMap_closed d).injective h⟩
  · rintro ⟨p, rfl, rfl⟩
    exact newMap_piece d p

theorem handle_mem_new_iff (z : UnitDisk E × UnitDisk F) :
    handleMap d z ∈ range (newMap d) ↔ ‖z.2.val‖ = 1 := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨p, -, hp⟩ := (newMap_eq_handleMap d y z).mp hy
    have he : p.2.val = z.2.val := congrArg (fun w : UnitDisk E × UnitDisk F ↦ w.2.val) hp
    exact he ▸ mem_sphere_zero_iff_norm.mp p.2.property
  · intro hz
    let p : UnitBall E × UnitSphere F :=
      ((unitBallHomeomorph E).symm z.1, ⟨z.2.val, mem_sphere_zero_iff_norm.mpr hz⟩)
    refine ⟨d.newPiece p, (newMap_eq_handleMap d (d.newPiece p) z).mpr ⟨p, rfl, ?_⟩⟩
    exact Prod.ext ((unitBallHomeomorph E).apply_symm_apply z.1) rfl

theorem new_cover : range (newMap d) ∪ range (handleMap d) = univ := by
  apply eq_univ_of_forall
  intro z
  have hz : z ∈ range (oldMap d) ∪ range (handleMap d) := by rw [old_cover]; trivial
  rcases hz with ⟨x, rfl⟩ | hz
  · have hx : x ∈ range d.oldExterior ∪ range d.oldPiece := by rw [d.old_cover]; trivial
    rcases hx with ⟨r, rfl⟩ | ⟨p, rfl⟩
    · exact Or.inl ⟨d.newExterior r, newMap_exterior d r⟩
    · exact Or.inr ⟨oldFace p, (old_face_identification d p).symm⟩
  · exact Or.inr hz

theorem newMap_closed [CompactSpace Y] : IsClosedEmbedding (newMap d) :=
  (newMap d).continuous.isClosedEmbedding (newMap_injective d)

def reverseHandle : C(UnitDisk F × UnitDisk E, Space d) :=
  (handleMap d).comp ⟨Prod.swap, continuous_swap⟩

theorem reverseHandle_closed : IsClosedEmbedding (reverseHandle d) :=
  (handleMap_closed d).comp (Homeomorph.prodComm (UnitDisk F) (UnitDisk E)).isClosedEmbedding

theorem reverse_cover : range (newMap d) ∪ range (reverseHandle d) = univ := by
  have he : range (reverseHandle d) = range (handleMap d) :=
    (Homeomorph.prodComm (UnitDisk F) (UnitDisk E)).surjective.range_comp (handleMap d)
  rw [he, new_cover]

theorem reverseHandle_mem_new_iff (z : UnitDisk F × UnitDisk E) :
    reverseHandle d z ∈ range (newMap d) ↔ ‖z.1.val‖ = 1 :=
  handle_mem_new_iff d z.swap

theorem core_boundary (u : UnitSphere E) :
    handleMap d (⟨u.val, sphere_subset_closedBall u.property⟩, ⟨0, by simp⟩) =
      oldMap d (d.attachingSphere u) :=
  (old_face_identification d (u, ballZero)).symm

theorem reverseCore_boundary (v : UnitSphere F) :
    reverseHandle d (⟨v.val, sphere_subset_closedBall v.property⟩, ⟨0, by simp⟩) =
      newMap d (d.beltSphere v) :=
  (newMap_piece d (ballZero, v)).symm

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody
