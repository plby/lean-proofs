import Wikipedia.SmoothSixDPoincare.FramedSurgeryExterior

/-!
# Exact closed-piece presentations of the original and new boundaries

Both boundaries are covered by the common exterior and their full closed
face. The two cross-piece intersections are exactly the common corner,
with no additional identifications.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem exterior_old_face_overlap (r : Exterior A) (p : UnitSphere E × MorseHandle.UnitDisk F) :
    exteriorOldMap A r = A.map p ↔
      ∃ q : UnitSphere E × UnitSphere F, r = exteriorCorner A q ∧
        p = (q.1, ⟨q.2.val, sphere_subset_closedBall q.2.property⟩) := by
  constructor
  · intro h
    have hn : ‖p.2.val‖ = 1 := by
      apply le_antisymm (mem_closedBall_zero_iff.mp p.2.property)
      apply le_of_not_gt
      intro hlt
      apply r.property
      rw [show r.val = A.map p from h]
      exact (face_mem_interior_iff A p.1 p.2).mpr hlt
    let q : UnitSphere E × UnitSphere F := (p.1, ⟨p.2.val, mem_sphere_zero_iff_norm.mpr hn⟩)
    exact ⟨q, Subtype.ext h, rfl⟩
  · rintro ⟨q, rfl, rfl⟩
    rfl

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem exterior_old_face_cover : range (exteriorOldMap A) ∪ range A.map = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ faceInterior A
  · obtain ⟨⟨u, v⟩, ⟨_, hv⟩, h⟩ := hx
    let w : MorseHandle.UnitDisk F := ⟨v, ball_subset_closedBall hv⟩
    exact Or.inr ⟨(u, w), (A.point u w).symm.trans h⟩
  · exact Or.inl ⟨⟨x, hx⟩, rfl⟩

variable (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

theorem exterior_new_face_overlap (r : Exterior A) (p : ClosedNewFace E F) :
    exteriorNewMap A n r = closedNewMap A n p ↔
      ∃ q : UnitSphere E × UnitSphere F, r = exteriorCorner A q ∧
        p = (⟨q.1.val, sphere_subset_closedBall q.1.property⟩, q.2) := by
  constructor
  · intro h
    have hu : p.1.val ≠ 0 := by
      intro hp
      have hp' : p = (⟨0, by simp⟩, p.2) := Prod.ext (Subtype.ext hp) rfl
      apply closedNewMap_zero_ne_old A n p.2 (exteriorToOldPatch A r)
      exact (congrArg (closedNewMap A n) hp').symm.trans h.symm
    let u : PuncturedBall E := ⟨p.1.val, hu, mem_closedBall_zero_iff.mp p.1.property⟩
    let s := (exchange E F).symm (u, p.2)
    have he : closedNewMap A n p = oldMap A n (oldClosedOverlap A s) :=
      closedNewMap_punctured A n u p.2
    have hold : exteriorOldMap A r =
        A.map (s.1, ⟨s.2.val, mem_closedBall_zero_iff.mpr s.2.property.2⟩) :=
      congrArg (fun z : oldPatch A => z.val) ((oldMap_isOpenEmbedding A n).injective (h.trans he))
    obtain ⟨q, hr, hp⟩ := (exterior_old_face_overlap A r _).mp hold
    have hs : s = (q.1, boundaryPoint q.2) :=
      Prod.ext (congrArg (fun z : UnitSphere E × MorseHandle.UnitDisk F => z.1) hp)
        (Subtype.ext (congrArg (fun z : UnitSphere E × MorseHandle.UnitDisk F => z.2.val) hp))
    have hrad : (u, p.2) = (boundaryPoint q.1, q.2) :=
      ((exchange E F).apply_symm_apply (u, p.2)).symm.trans
        ((congrArg (exchange E F) hs).trans (exchange_boundary q.1 q.2))
    refine ⟨q, hr, ?_⟩
    exact Prod.ext (Subtype.ext
      (congrArg (fun z : PuncturedBall E × UnitSphere F => z.1.val) hrad))
      (congrArg (fun z : PuncturedBall E × UnitSphere F => z.2) hrad)
  · rintro ⟨q, rfl, rfl⟩
    exact exteriorNewMap_corner A n q

theorem exterior_new_face_cover :
    range (exteriorNewMap A n) ∪ range (closedNewMap A n) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain (⟨x, rfl⟩ | ⟨y, rfl⟩) := cover A n q
  · by_cases hx : x.val ∈ faceInterior A
    · obtain ⟨⟨u, v⟩, ⟨_, hv⟩, h⟩ := hx
      let w : MorseHandle.UnitDisk F := ⟨v, ball_subset_closedBall hv⟩
      have hmap : A.map (u, w) = x.val := (A.point u w).symm.trans h
      have hv0 : v ≠ 0 := by
        intro hz
        apply x.property
        rw [← hmap]
        exact (face_mem_core_iff A u w).mpr hz
      let z : UnitSphere E × PuncturedBall F :=
        (u, ⟨v, hv0, (mem_ball_zero_iff.mp hv).le⟩)
      let t := exchange E F z
      refine Or.inr ⟨(⟨t.1.val, mem_closedBall_zero_iff.mpr t.1.property.2⟩, t.2), ?_⟩
      exact (closedNewMap_punctured A n t.1 t.2).trans
        ((newOuterMap_exchange A n z).trans (congrArg (oldMap A n) (Subtype.ext hmap)))
    · exact Or.inl ⟨⟨x.val, hx⟩, rfl⟩
  · exact Or.inr ⟨(⟨y.1.val, mem_closedBall_zero_iff.mpr
      (mem_ball_zero_iff.mp y.1.property).le⟩, y.2), closedNewMap_open A n y⟩

end Wikipedia.SmoothSixDPoincare.FramedSurgery
