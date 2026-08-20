import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchData
import ErdosProblems.Erdos733.ST.StraightSegmentClosedBallGateCut

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryCrossingLocalBranchGateCarrier]
lemma OrdinaryCrossingLocalBranchGateCarrier
    (Q : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (branch : OrdinaryCrossingLocalBranchData Q p radius) :
    Metric.closedBall p radius ∩ Q.carrier =
      segment ℝ branch.beforeGate p ∪ segment ℝ p branch.afterGate := by
-- BODY
  have hbefore0 : branch.beforeIndex < Q.vertices.length :=
    Nat.lt_of_succ_lt branch.beforeIndex_valid
  have hafter0 : branch.afterIndex < Q.vertices.length :=
    Nat.lt_of_succ_lt branch.afterIndex_valid
  let vb := Q.vertices.get ⟨branch.beforeIndex, hbefore0⟩
  let vb1 := Q.vertices.get ⟨branch.beforeIndex + 1, branch.beforeIndex_valid⟩
  let va := Q.vertices.get ⟨branch.afterIndex, hafter0⟩
  let va1 := Q.vertices.get ⟨branch.afterIndex + 1, branch.afterIndex_valid⟩
  have hbeforeRay : branch.beforeGate ∈ openSegment ℝ p vb := by
    simpa only [vb, List.get_eq_getElem, openSegment_symm ℝ] using
      branch.beforeGate_open
  have hafterRay : branch.afterGate ∈ openSegment ℝ p va1 := by
    simpa only [va1, List.get_eq_getElem] using branch.afterGate_open
  have hbeforeCut := StraightSegmentClosedBallGateCut p branch.beforeGate vb radius
    branch.radius_pos hbeforeRay branch.beforeGate_on_sphere
  have hafterCut := StraightSegmentClosedBallGateCut p branch.afterGate va1 radius
    branch.radius_pos hafterRay branch.afterGate_on_sphere
  rw [branch.closedBall_carrier_eq]
  change Metric.closedBall p radius ∩
      (segment ℝ vb vb1 ∪ segment ℝ va va1) = _
  rcases branch.center_case with hsame | hlisted
  · have hva : va = vb := by
      simp only [va, vb, List.get_eq_getElem, hsame.1]
    have hva1 : va1 = vb1 := by
      simp only [va1, vb1, List.get_eq_getElem, hsame.1]
    rw [hva, hva1, Set.union_self]
    have hpOpen : p ∈ openSegment ℝ vb vb1 := by
      simpa only [vb, vb1, List.get_eq_getElem] using hsame.2
    have hpSeg : p ∈ segment ℝ vb vb1 :=
      openSegment_subset_segment ℝ _ _ hpOpen
    have hsplit : segment ℝ vb vb1 =
          segment ℝ vb p ∪ segment ℝ p vb1 := by
      apply Set.Subset.antisymm
      · intro z hz
        by_cases hzleft : z = vb
        · left
          simpa [hzleft] using left_mem_segment ℝ vb p
        by_cases hzright : z = vb1
        · right
          simpa [hzright] using right_mem_segment ℝ p vb1
        have hzopen : z ∈ openSegment ℝ vb vb1 :=
          mem_openSegment_of_ne_left_right (Ne.symm hzleft)
            (Ne.symm hzright) hz
        have hpRange : p ∈ Set.range
            (AffineMap.lineMap vb vb1 : ℝ → EuclideanSpace ℝ (Fin 2)) := by
          rw [openSegment_eq_image_lineMap] at hpOpen
          rcases hpOpen with ⟨t, _ht, htp⟩
          exact ⟨t, htp⟩
        rcases openSegment_subset_union vb vb1 hpRange hzopen with hzcenter | hzside
        · subst z
          exact Or.inl (right_mem_segment ℝ _ _)
        · rcases hzside with hzbefore | hzafter
          · exact Or.inl (openSegment_subset_segment ℝ _ _ hzbefore)
          · exact Or.inr (openSegment_subset_segment ℝ _ _ hzafter)
      · exact Set.union_subset
          ((convex_segment _ _).segment_subset
            (left_mem_segment ℝ _ _) hpSeg)
          ((convex_segment _ _).segment_subset hpSeg
            (right_mem_segment ℝ _ _))
    rw [hsplit, Set.inter_union_distrib_left]
    have hbeforeCut' : Metric.closedBall p radius ∩ segment ℝ vb p =
        segment ℝ branch.beforeGate p := by
      simpa only [segment_symm ℝ] using hbeforeCut
    have hafterCut' : Metric.closedBall p radius ∩ segment ℝ p vb1 =
        segment ℝ p branch.afterGate := by
      simpa only [hva1] using hafterCut
    rw [hbeforeCut', hafterCut']
  · have hvb1 : vb1 = p := by
      calc
        vb1 = Q.vertices[branch.beforeIndex + 1] := rfl
        _ = Q.vertices[branch.afterIndex] := by
          apply congrArg Q.vertices.get
          exact Fin.ext hlisted.1.symm
        _ = p := hlisted.2.symm
    have hva : va = p := by
      simp only [va, List.get_eq_getElem, ← hlisted.2]
    rw [hvb1, hva, Set.inter_union_distrib_left]
    have hbeforeCut' : Metric.closedBall p radius ∩ segment ℝ vb p =
        segment ℝ branch.beforeGate p := by
      simpa only [segment_symm ℝ] using hbeforeCut
    rw [hbeforeCut', hafterCut]
