import StackExchange.Puzzling139335.StraightBranchCount

/-!
# An actual two-segment boundary certificate

Two straight local branches of a Jordan boundary give two nondegenerate
segments meeting only at the vertex.  Their union agrees with the complete
boundary in a neighborhood of that vertex.
-/

open Set

namespace Puzzling139335

/-- Equality of germs is preserved by taking the union of two sets. -/
theorem SameBoundaryGerm.union {A B D E : Set Plane} {v : Plane}
    (hAB : SameBoundaryGerm A B v) (hDE : SameBoundaryGerm D E v) :
    SameBoundaryGerm (A ∪ D) (B ∪ E) v := by
  obtain ⟨r, hr, hAB⟩ := hAB
  obtain ⟨s, hs, hDE⟩ := hDE
  refine ⟨min r s, lt_min hr hs, ?_⟩
  ext x
  constructor
  · rintro ⟨hxball, hxA | hxD⟩
    · exact ⟨hxball, Or.inl (((Set.ext_iff.mp hAB x).mp
        ⟨Metric.ball_subset_ball (min_le_left r s) hxball, hxA⟩).2)⟩
    · exact ⟨hxball, Or.inr (((Set.ext_iff.mp hDE x).mp
        ⟨Metric.ball_subset_ball (min_le_right r s) hxball, hxD⟩).2)⟩
  · rintro ⟨hxball, hxB | hxE⟩
    · exact ⟨hxball, Or.inl (((Set.ext_iff.mp hAB x).mpr
        ⟨Metric.ball_subset_ball (min_le_left r s) hxball, hxB⟩).2)⟩
    · exact ⟨hxball, Or.inr (((Set.ext_iff.mp hDE x).mpr
        ⟨Metric.ball_subset_ball (min_le_right r s) hxball, hxE⟩).2)⟩

/-- A boundary with two straight branches is locally exactly the union of
two nondegenerate straight segments meeting only at its vertex. -/
theorem HasStraightBranchCount.exists_two_segments {C : Set Plane} {v : Plane}
    (h : HasStraightBranchCount C v 2) :
    ∃ a b : Plane, a ≠ v ∧ b ≠ v ∧
      segment ℝ v a ⊆ C ∧ segment ℝ v b ⊆ C ∧
      segment ℝ v a ∩ segment ℝ v b = {v} ∧
      SameBoundaryGerm C (segment ℝ v a ∪ segment ℝ v b) v := by
  obtain ⟨q, A, B, hcut, hn⟩ := h
  have hcount : HasStraightBranchCount C v 2 := ⟨q, A, B, hcut, hn⟩
  obtain ⟨w, hw, hwA⟩ := hcount.two_implies_endpoint_arc_straight hcut.fst hcut.fst_subset
  obtain ⟨z, hz, hzB⟩ := hcount.two_implies_endpoint_arc_straight hcut.snd hcut.snd_subset
  have hvq : v ≠ q := by
    obtain ⟨f, _, hi, _, h0, h1⟩ := hcut.fst
    intro heq
    exact zero_ne_one (hi Schoenflies.zero_mem_I Schoenflies.one_mem_I
      (h0.trans (heq.trans h1.symm)))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (isClosed_singleton : IsClosed ({q} : Set Plane)).isOpen_compl v hvq
  obtain ⟨a, ha, haSmall⟩ := exists_initial_segment_subset_ball hw hr
  obtain ⟨b, hb, hbSmall⟩ := exists_initial_segment_subset_ball hz hr
  have haA : segment ℝ v a ⊆ A := fun x hx => hwA (haSmall hx).1
  have hbB : segment ℝ v b ⊆ B := fun x hx => hzB (hbSmall hx).1
  have haGerm : SameBoundaryGerm A (segment ℝ v a) v :=
    nested_arcs_sameBoundaryGerm hcut.fst (Schoenflies.isArcBetween_segment ha.symm) haA
  have hbGerm : SameBoundaryGerm B (segment ℝ v b) v :=
    nested_arcs_sameBoundaryGerm hcut.snd (Schoenflies.isArcBetween_segment hb.symm) hbB
  refine ⟨a, b, ha, hb, haA.trans hcut.fst_subset, hbB.trans hcut.snd_subset, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      have hxAB : x ∈ A ∩ B := ⟨haA hx.1, hbB hx.2⟩
      have hxpair : x ∈ ({v, q} : Set Plane) := hcut.inter_eq ▸ hxAB
      rcases mem_insert_iff.mp hxpair with hxv | hxq
      · exact hxv
      · exact False.elim ((hball (haSmall hx.1).2) hxq)
    · intro x hx
      rw [mem_singleton_iff] at hx
      subst x
      exact ⟨left_mem_segment ℝ v a, left_mem_segment ℝ v b⟩
  · have h := haGerm.union hbGerm
    rwa [hcut.union_eq] at h

end Puzzling139335
