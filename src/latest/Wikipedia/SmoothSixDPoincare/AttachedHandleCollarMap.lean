import Wikipedia.SmoothSixDPoincare.AttachedHandleCollarDepth
import Wikipedia.SmoothSixDPoincare.FramedSurgeryBodyBoundary
import Wikipedia.SmoothSixDPoincare.ClosedPieceMaps

/-!
# Assemble the whole surgery-boundary collar with its original zero end

The retained old exterior and the entire new face give a closed cover of
the original surgery boundary. Their cylinder maps agree at every corner
and glue continuously. The actual boundary inclusion is the zero end, and
the continuous attached-body depth recovers the same time on both pieces.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

variable {E F G H X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (PuncturedHandle.UnitSphere E) F X)
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  (i : C(X, Y)) (C : InwardBoundaryCollar i) (hi : IsClosedEmbedding i)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

def collarOldBoundary : C(Exterior A × unitInterval, Boundary A n × unitInterval) :=
  ⟨fun q => (exteriorNewMap A n q.1, q.2),
    ((exteriorNewMap A n).continuous.comp continuous_fst).prodMk continuous_snd⟩

def collarNewBoundary : C(ClosedNewFace E F × unitInterval, Boundary A n × unitInterval) :=
  ⟨fun q => (closedNewMap A n q.1, q.2),
    ((closedNewMap A n).continuous.comp continuous_fst).prodMk continuous_snd⟩

theorem collarOldBoundary_isClosedEmbedding : IsClosedEmbedding (collarOldBoundary A n) :=
  (exteriorNewMap_isClosedEmbedding A n).prodMap IsClosedEmbedding.id

omit [CompactSpace X] in
theorem collarNewBoundary_isClosedEmbedding : IsClosedEmbedding (collarNewBoundary A n) :=
  (closedNewMap_isClosedEmbedding A n).prodMap IsClosedEmbedding.id

omit [FiniteDimensional ℝ F] [CompactSpace X] in
theorem collarBoundary_cover :
    range (collarOldBoundary A n) ∪ range (collarNewBoundary A n) = univ := by
  apply eq_univ_of_forall
  rintro ⟨z, t⟩
  have hz : z ∈ range (exteriorNewMap A n) ∪ range (closedNewMap A n) :=
    (exterior_new_face_cover A n).symm ▸ mem_univ z
  rcases hz with ⟨r, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl ⟨(r, t), rfl⟩
  · exact Or.inr ⟨(p, t), rfl⟩

def oldCollarMap : C(Exterior A × unitInterval, AttachedBody A i) :=
  (FaceAttachment.oldMap (bodyFaceMap A i)).comp
    (C.map.comp ⟨fun q => (q.1.val, HandleCollarCoordinates.oldTime q.2),
      (continuous_subtype_val.comp continuous_fst).prodMk
        (((continuous_subtype_val.comp continuous_snd).div_const 2).subtype_mk _)⟩)

omit [CompactSpace X] [T2Space Y] [CompactSpace Y] in
theorem collar_pieces_agree (a : Exterior A × unitInterval) (b : ClosedNewFace E F × unitInterval)
    (hab : collarOldBoundary A n a = collarNewBoundary A n b) :
    oldCollarMap A i C a =
      CollaredHandleEmbedding.newCollarMap A.map i C hi.injective
        A.closedEmbedding.injective b := by
  rcases a with ⟨r, t⟩
  rcases b with ⟨p, s⟩
  have hts : t = s := congrArg Prod.snd hab
  subst s
  have hp : exteriorNewMap A n r = closedNewMap A n p := congrArg Prod.fst hab
  obtain ⟨q, rfl, rfl⟩ := (exterior_new_face_overlap A n r p).mp hp
  exact (CollaredHandleEmbedding.newCollarMap_corner A.map i C hi.injective
    A.closedEmbedding.injective q.1 q.2 t).symm

def collarMap : C(Boundary A n × unitInterval, AttachedBody A i) :=
  ClosedCover.mapOfClosedPieces (collarOldBoundary A n) (collarNewBoundary A n)
    (collarOldBoundary_isClosedEmbedding A n) (collarNewBoundary_isClosedEmbedding A n)
    (collarBoundary_cover A n) (oldCollarMap A i C)
    (CollaredHandleEmbedding.newCollarMap A.map i C hi.injective A.closedEmbedding.injective)
    (collar_pieces_agree A i C hi n)

omit [T2Space Y] [CompactSpace Y] in
theorem collarMap_exterior (r : Exterior A) (t : unitInterval) :
    collarMap A i C hi n (exteriorNewMap A n r, t) =
      FaceAttachment.oldMap (bodyFaceMap A i) (C.map (r.val, HandleCollarCoordinates.oldTime t)) :=
  ClosedCover.mapOfClosedPieces_left (collarOldBoundary A n) (collarNewBoundary A n)
    (collarOldBoundary_isClosedEmbedding A n) (collarNewBoundary_isClosedEmbedding A n)
    (collarBoundary_cover A n) (oldCollarMap A i C)
    (CollaredHandleEmbedding.newCollarMap A.map i C hi.injective A.closedEmbedding.injective)
    (collar_pieces_agree A i C hi n) (r, t)

omit [T2Space Y] [CompactSpace Y] in
theorem collarMap_new (p : ClosedNewFace E F) (t : unitInterval) :
    collarMap A i C hi n (closedNewMap A n p, t) =
      CollaredHandleEmbedding.newCollarMap A.map i C hi.injective A.closedEmbedding.injective
        (p, t) :=
  ClosedCover.mapOfClosedPieces_right (collarOldBoundary A n) (collarNewBoundary A n)
    (collarOldBoundary_isClosedEmbedding A n) (collarNewBoundary_isClosedEmbedding A n)
    (collarBoundary_cover A n) (oldCollarMap A i C)
    (CollaredHandleEmbedding.newCollarMap A.map i C hi.injective A.closedEmbedding.injective)
    (collar_pieces_agree A i C hi n) (p, t)

theorem collarMap_zero (z : Boundary A n) :
    collarMap A i C hi n (z, 0) = boundaryBodyMap A i n hi z := by
  have hz : z ∈ range (exteriorNewMap A n) ∪ range (closedNewMap A n) :=
    (exterior_new_face_cover A n).symm ▸ mem_univ z
  rcases hz with ⟨r, rfl⟩ | ⟨p, rfl⟩
  · rw [collarMap_exterior]
    have ht : HandleCollarCoordinates.oldTime 0 = 0 := by
      apply Subtype.ext
      norm_num [HandleCollarCoordinates.oldTime, HandleCollarCoordinates.time]
    rw [ht, C.zero, boundaryBodyMap_exterior]
  · rw [collarMap_new]
    exact (CollaredHandleEmbedding.newCollarMap_zero A.map i C hi.injective
      A.closedEmbedding.injective p.1 p.2).trans (boundaryBodyMap_newFace A i n hi p).symm

omit [T2Space Y] [CompactSpace Y] in
theorem collarMap_depth (z : Boundary A n) (t : unitInterval) :
    attachedCollarDepth A i C (collarMap A i C hi n (z, t)) = HandleCollarCoordinates.time t := by
  have hz : z ∈ range (exteriorNewMap A n) ∪ range (closedNewMap A n) :=
    (exterior_new_face_cover A n).symm ▸ mem_univ z
  rcases hz with ⟨r, rfl⟩ | ⟨p, rfl⟩
  · rw [collarMap_exterior]
    have hr : r.val ∉ A.interiorImage := by
      simpa only [A.interiorImage_eq_chart, faceInterior] using r.property
    exact attachedCollarDepth_exterior A i C r.val hr (HandleCollarCoordinates.oldTime t)
  · rw [collarMap_new]
    exact attachedCollarDepth_new_collar A i C hi.injective (p, t)

omit [T2Space Y] [CompactSpace Y] in
theorem collarMap_time_injective (a b : Boundary A n × unitInterval)
    (h : collarMap A i C hi n a = collarMap A i C hi n b) : a.2 = b.2 := by
  have hd := congrArg (attachedCollarDepth A i C) h
  rw [collarMap_depth, collarMap_depth] at hd
  apply Subtype.ext
  change (a.2 : ℝ) / 2 = (b.2 : ℝ) / 2 at hd
  linarith

end Wikipedia.SmoothSixDPoincare.FramedSurgery
