import Wikipedia.SmoothSixDPoincare.FramedSurgeryRetainedBoundaryUpdate

/-!
# The retained second face avoids the entire first closed new face

The exact retained point map lies in the original old patch. The closed
piece incidence theorem shows that points outside the first attaching face
cannot meet its new closed face, including the common corner.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

omit [FiniteDimensional ℝ F] in
theorem oldMap_ne_closedNewMap_of_not_mem (x : oldPatch A) (hx : x.val ∉ range A.map)
    (p : ClosedNewFace E F) : oldMap A n x ≠ closedNewMap A n p := by
  intro he
  let r : Exterior A := ⟨x.val, fun h => hx (faceInterior_subset_range h)⟩
  have he' : exteriorNewMap A n r = closedNewMap A n p := he
  obtain ⟨q, hr, -⟩ := (exterior_new_face_overlap A n r p).mp he'
  apply hx
  exact ⟨(q.1, ⟨q.2.val, sphere_subset_closedBall q.2.property⟩),
    (congrArg (fun z : Exterior A => z.val) hr).symm⟩

namespace SmoothBoundaryData

variable {A n} (P : SmoothBoundaryData A n)
  {D K B N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D K} [TopologicalSpace B] [ChartedSpace K B]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [CompactSpace (B × MorseHandle.UnitDisk N)]
  (C : SmoothClosedFace I J B N X) (hC : Disjoint (range C.map) (range A.map))

theorem retainClosedDisjointFace_map (z : B × MorseHandle.UnitDisk N)
    (x : oldPatch A) (hx : x.val = C.map z) :
    letI := P.charted
    (P.retainClosedDisjointFace C hC).map z = oldMap A n x := by
  let _ := P.charted
  exact P.retainFace_map
    (C.avoidClosed (range A.map) A.closedEmbedding.isClosed_range hC)
    (subset_oldPatch_of_disjoint_face
      (C.avoidClosed_disjoint (range A.map) A.closedEmbedding.isClosed_range hC)) z x hx

theorem retainClosedDisjointFace_disjoint_closedNewMap :
    letI := P.charted
    Disjoint (range (P.retainClosedDisjointFace C hC).map) (range (closedNewMap A n)) := by
  let _ := P.charted
  rw [disjoint_left]
  rintro y ⟨z, rfl⟩ ⟨p, hp⟩
  have hx : C.map z ∉ range A.map := fun h => disjoint_left.mp hC (mem_range_self z) h
  let x : oldPatch A := ⟨C.map z, fun h => hx
    (faceInterior_subset_range (core_subset_faceInterior A h))⟩
  have he := P.retainClosedDisjointFace_map C hC z x rfl
  exact oldMap_ne_closedNewMap_of_not_mem A n x hx p (he.symm.trans hp.symm)

theorem closedNewMap_not_mem_retainedInterior (p : ClosedNewFace E F) :
    letI := P.charted
    closedNewMap A n p ∉ (P.retainClosedDisjointFace C hC).interiorImage := by
  let _ := P.charted
  intro hp
  exact disjoint_left.mp (P.retainClosedDisjointFace_disjoint_closedNewMap C hC)
    ((P.retainClosedDisjointFace C hC).interiorImage_subset_range hp) (mem_range_self p)

end SmoothBoundaryData

end Wikipedia.SmoothSixDPoincare.FramedSurgery
