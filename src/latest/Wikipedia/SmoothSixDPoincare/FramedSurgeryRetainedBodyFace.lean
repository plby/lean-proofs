import Wikipedia.SmoothSixDPoincare.FramedSurgeryBodyBoundary
import Wikipedia.SmoothSixDPoincare.FramedSurgeryRetainedFace
import Wikipedia.SmoothSixDPoincare.SmoothClosedFaceTargetRestriction

/-!
# Retained smooth faces keep their original maps into the whole body

When a full framed chart avoids the old attaching face, its retained chart
in the constructed smooth boundary has exactly the old body image. This
holds for the whole chart target as well as every closed-face coordinate.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  {A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X] [CompactSpace X] in
theorem faceInterior_subset_range : faceInterior A ⊆ range A.map := by
  rintro x ⟨⟨u, v⟩, ⟨_, hv⟩, hx⟩
  exact ⟨(u, ⟨v, ball_subset_closedBall hv⟩),
    (A.point u ⟨v, ball_subset_closedBall hv⟩).symm.trans hx⟩

omit [FiniteDimensional ℝ F] [CompactSpace X] in
theorem subset_oldPatch_of_disjoint_face {S : Set X} (hS : Disjoint S (range A.map)) :
    S ⊆ oldPatch A := by
  intro x hx hcore
  exact disjoint_left.mp hS hx (faceInterior_subset_range (core_subset_faceInterior A hcore))

namespace SmoothBoundaryData

variable {n : ℕ} [Fact (Module.finrank ℝ F = n + 1)] (P : SmoothBoundaryData A n)
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  (i : C(X, Y)) (hi : IsClosedEmbedding i)
  {D K B N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D K} [TopologicalSpace B] [ChartedSpace K B]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [CompactSpace (B × MorseHandle.UnitDisk N)]
  (C : SmoothClosedFace I J B N X)
  (havoid : Disjoint C.chart.target (range A.map))

def retainDisjointFace : letI := P.charted; SmoothClosedFace I J B N (Boundary A n) :=
  P.retainFace C (subset_oldPatch_of_disjoint_face havoid)

theorem retainDisjointFace_bodyMap (z : B × MorseHandle.UnitDisk N) :
    letI := P.charted
    boundaryBodyMap A i n hi ((P.retainDisjointFace C havoid).map z) =
      FaceAttachment.oldMap (bodyFaceMap A i) (i (C.map z)) := by
  let _ := P.charted
  have ht : C.map z ∈ C.chart.target := by
    rw [← C.point z.1 z.2]
    exact C.chart.map_source (C.source ⟨mem_univ _, z.2.property⟩)
  let x : oldPatch A := ⟨C.map z, subset_oldPatch_of_disjoint_face havoid ht⟩
  have he := P.retainFace_map C (subset_oldPatch_of_disjoint_face havoid) z x rfl
  change boundaryBodyMap A i n hi ((P.retainFace C _).map z) = _
  rw [he]
  apply boundaryBodyMap_old_exterior
  intro hx
  exact disjoint_left.mp havoid ht (faceInterior_subset_range hx)

theorem retainDisjointFace_chart_bodyImage :
    letI := P.charted
    boundaryBodyMap A i n hi '' (P.retainDisjointFace C havoid).chart.target =
      (FaceAttachment.oldMap (bodyFaceMap A i) ∘ i) '' C.chart.target := by
  let _ := P.charted
  change boundaryBodyMap A i n hi '' (P.retainFace C _).chart.target = _
  rw [P.retainFace_chart_target]
  ext z
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x.val, hx, ?_⟩
    exact (boundaryBodyMap_old_exterior A i n hi x
      (fun h => disjoint_left.mp havoid hx (faceInterior_subset_range h))).symm
  · rintro ⟨x, hx, rfl⟩
    let x' : oldPatch A := ⟨x, subset_oldPatch_of_disjoint_face havoid hx⟩
    refine ⟨oldMap A n x', ⟨x', hx, rfl⟩, ?_⟩
    exact boundaryBodyMap_old_exterior A i n hi x'
      (fun h => disjoint_left.mp havoid hx (faceInterior_subset_range h))

theorem retainDisjointFace_chart_avoids_wholeHandle :
    letI := P.charted
    Disjoint (boundaryBodyMap A i n hi '' (P.retainDisjointFace C havoid).chart.target)
      (range (FaceAttachment.handleMap (bodyFaceMap A i))) := by
  let _ := P.charted
  rw [P.retainDisjointFace_chart_bodyImage i hi C havoid, disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨k, hk⟩
  obtain ⟨u, hu, -⟩ :=
    (FaceAttachment.oldMap_eq_handleMap (bodyFaceMap A i)
      (bodyFaceMap_injective A i hi.injective) _ _).mp hk.symm
  apply disjoint_left.mp havoid hx
  exact ⟨wholeFaceCoordinates E F u, hi.injective hu⟩

/-- Disjointness of the closed faces suffices: the framed neighborhood is restricted here. -/
def retainClosedDisjointFace (hdisjoint : Disjoint (range C.map) (range A.map)) :
    letI := P.charted; SmoothClosedFace I J B N (Boundary A n) :=
  P.retainDisjointFace
    (C.avoidClosed (range A.map) A.closedEmbedding.isClosed_range hdisjoint)
    (C.avoidClosed_disjoint (range A.map) A.closedEmbedding.isClosed_range hdisjoint)

theorem retainClosedDisjointFace_bodyMap
    (hdisjoint : Disjoint (range C.map) (range A.map)) (z : B × MorseHandle.UnitDisk N) :
    letI := P.charted
    boundaryBodyMap A i n hi ((P.retainClosedDisjointFace C hdisjoint).map z) =
      FaceAttachment.oldMap (bodyFaceMap A i) (i (C.map z)) :=
  P.retainDisjointFace_bodyMap i hi
    (C.avoidClosed (range A.map) A.closedEmbedding.isClosed_range hdisjoint)
    (C.avoidClosed_disjoint (range A.map) A.closedEmbedding.isClosed_range hdisjoint) z

theorem retainClosedDisjointFace_chart_bodyImage
    (hdisjoint : Disjoint (range C.map) (range A.map)) :
    letI := P.charted
    boundaryBodyMap A i n hi '' (P.retainClosedDisjointFace C hdisjoint).chart.target =
      (FaceAttachment.oldMap (bodyFaceMap A i) ∘ i) ''
        ((range A.map)ᶜ ∩ C.chart.target) :=
  P.retainDisjointFace_chart_bodyImage i hi
    (C.avoidClosed (range A.map) A.closedEmbedding.isClosed_range hdisjoint)
    (C.avoidClosed_disjoint (range A.map) A.closedEmbedding.isClosed_range hdisjoint)

theorem retainClosedDisjointFace_chart_avoids_wholeHandle
    (hdisjoint : Disjoint (range C.map) (range A.map)) :
    letI := P.charted
    Disjoint (boundaryBodyMap A i n hi '' (P.retainClosedDisjointFace C hdisjoint).chart.target)
      (range (FaceAttachment.handleMap (bodyFaceMap A i))) :=
  P.retainDisjointFace_chart_avoids_wholeHandle i hi
    (C.avoidClosed (range A.map) A.closedEmbedding.isClosed_range hdisjoint)
    (C.avoidClosed_disjoint (range A.map) A.closedEmbedding.isClosed_range hdisjoint)

end SmoothBoundaryData

end Wikipedia.SmoothSixDPoincare.FramedSurgery
