import ErdosProblems.Erdos957.CollisionGlue
import ErdosProblems.Erdos957.Case13SideUniqueness
import ErdosProblems.Erdos957.Case3SameSide

/-!
# Finite realized-role collision dispatch for Erdős 957

This file closes the part of the seven-window no-three theorem involving
only formula-retaining Case 1 and Case 3 rows.  The genuinely consecutive
branch uses the checked flat-source incidence exclusion.  Every other
three-source placement contains two sources three or four cyclic positions
apart; the production bisector-frame estimates put those sources more than
two units apart, whereas a common Case 1/3 recipient would put them at
distance at most two.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957RoleCollisions

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CollisionInstantiation
open Erdos957Case13SideUniqueness
open Erdos957MiddleLocalization

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

abbrev Case13Row (s : Source P W) :=
  ActualRow (P := P) (C := F.chart) (sourceIndex P W s.1 s.property)

lemma case13Row_adj_source {s : Source P W} (R : Case13Row (F := F) s)
    {v : Vertex A} (hv : 0 < R.tokens v) :
    (unitDistanceGraph A).Adj s.1 v := by
  simpa [sourceIndex] using R.adj_source_of_tokens_pos hv

lemma source_dist_le_two_of_case13_common_target
    {s t : Source P W} (Rs : Case13Row (F := F) s)
    (Rt : Case13Row (F := F) t) {v : Vertex A}
    (hs : 0 < Rs.tokens v) (ht : 0 < Rt.tokens v) :
    dist (s.1 : Point) (t.1 : Point) ≤ 2 := by
  have hsv := case13Row_adj_source Rs hs
  have htv := case13Row_adj_source Rt ht
  calc
    dist (s.1 : Point) (t.1 : Point) ≤
        dist (s.1 : Point) (v : Point) + dist (v : Point) (t.1 : Point) :=
      dist_triangle _ _ _
    _ = 2 := by
      rw [show dist (s.1 : Point) (v : Point) = 1 by
            simpa [unitDistanceGraph] using hsv,
          show dist (v : Point) (t.1 : Point) = 1 by
            simpa [unitDistanceGraph, dist_comm] using htv]
      norm_num

lemma no_case13_common_target_third_successor
    {s t : Source P W} (Rs : Case13Row (F := F) s)
    (Rt : Case13Row (F := F) t) {v : Vertex A}
    (hs : 0 < Rs.tokens v) (ht : 0 < Rt.tokens v)
    (hst : sourceIndex P W t.1 t.property =
      (P.next ^ 3) (sourceIndex P W s.1 s.property)) : False := by
  have hfar := Erdos957GeometryLocalityBridge.dist_third_successor_gt_two
    F (sourceIndex P W s.1 s.property)
      (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
  have hdist : dist (s.1 : Point) (t.1 : Point) ≤ 2 :=
    source_dist_le_two_of_case13_common_target Rs Rt hs ht
  have hpoints :
      ((((P.next ^ 3) (sourceIndex P W s.1 s.property)).1 : Vertex A) : Point) =
        (t.1 : Point) := by
    simpa [sourceIndex] using congrArg (fun x : {p // p ∈ P.H} ↦
      (x.1 : Point)) hst.symm
  rw [hpoints] at hfar
  exact (not_lt_of_ge hdist) hfar

lemma no_case13_common_target_fourth_successor
    {s t : Source P W} (Rs : Case13Row (F := F) s)
    (Rt : Case13Row (F := F) t) {v : Vertex A}
    (hs : 0 < Rs.tokens v) (ht : 0 < Rt.tokens v)
    (hst : sourceIndex P W t.1 t.property =
      (P.next ^ 4) (sourceIndex P W s.1 s.property)) : False := by
  have hfar := Erdos957GeometryLocalityBridge.dist_fourth_successor_gt_two
    F (sourceIndex P W s.1 s.property)
      (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
  have hdist : dist (s.1 : Point) (t.1 : Point) ≤ 2 :=
    source_dist_le_two_of_case13_common_target Rs Rt hs ht
  have hpoints :
      ((((P.next ^ 4) (sourceIndex P W s.1 s.property)).1 : Vertex A) : Point) =
        (t.1 : Point) := by
    simpa [sourceIndex] using congrArg (fun x : {p // p ∈ P.H} ↦
      (x.1 : Point)) hst.symm
  rw [hpoints] at hfar
  exact (not_lt_of_ge hdist) hfar

lemma no_case13_common_target_third_predecessor
    {s t : Source P W} (Rs : Case13Row (F := F) s)
    (Rt : Case13Row (F := F) t) {v : Vertex A}
    (hs : 0 < Rs.tokens v) (ht : 0 < Rt.tokens v)
    (hst : sourceIndex P W t.1 t.property =
      ((P.next⁻¹) ^ 3) (sourceIndex P W s.1 s.property)) : False := by
  have hfar := Erdos957GeometryLocalityBridge.dist_third_predecessor_gt_two
    F (sourceIndex P W s.1 s.property)
      (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
  have hdist : dist (s.1 : Point) (t.1 : Point) ≤ 2 :=
    source_dist_le_two_of_case13_common_target Rs Rt hs ht
  have hpoints :
      (((((P.next⁻¹) ^ 3) (sourceIndex P W s.1 s.property)).1 : Vertex A) : Point) =
        (t.1 : Point) := by
    simpa [sourceIndex] using congrArg (fun x : {p // p ∈ P.H} ↦
      (x.1 : Point)) hst.symm
  rw [hpoints] at hfar
  exact (not_lt_of_ge hdist) hfar

lemma no_case13_common_target_fourth_predecessor
    {s t : Source P W} (Rs : Case13Row (F := F) s)
    (Rt : Case13Row (F := F) t) {v : Vertex A}
    (hs : 0 < Rs.tokens v) (ht : 0 < Rt.tokens v)
    (hst : sourceIndex P W t.1 t.property =
      ((P.next⁻¹) ^ 4) (sourceIndex P W s.1 s.property)) : False := by
  have hfar := Erdos957GeometryLocalityBridge.dist_fourth_predecessor_gt_two
    F (sourceIndex P W s.1 s.property)
      (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
  have hdist : dist (s.1 : Point) (t.1 : Point) ≤ 2 :=
    source_dist_le_two_of_case13_common_target Rs Rt hs ht
  have hpoints :
      (((((P.next⁻¹) ^ 4) (sourceIndex P W s.1 s.property)).1 : Vertex A) : Point) =
        (t.1 : Point) := by
    simpa [sourceIndex] using congrArg (fun x : {p // p ∈ P.H} ↦
      (x.1 : Point)) hst.symm
  rw [hpoints] at hfar
  exact (not_lt_of_ge hdist) hfar

lemma no_case13_common_target_prev_self_next
    (hA : IsOneSeparated A)
    {p s n : Source P W}
    (Rp : Case13Row (F := F) p) (Rs : Case13Row (F := F) s)
    (Rn : Case13Row (F := F) n) {v : Vertex A}
    (hp : 0 < Rp.tokens v) (hs : 0 < Rs.tokens v)
    (hn : 0 < Rn.tokens v)
    (hprev : sourceIndex P W p.1 p.property =
      P.next⁻¹ (sourceIndex P W s.1 s.property))
    (hnext : sourceIndex P W n.1 n.property =
      P.next (sourceIndex P W s.1 s.property)) : False := by
  let i := sourceIndex P W s.1 s.property
  have hsv := case13Row_adj_source Rs hs
  have hpv := (unitDistanceGraph A).adj_symm (case13Row_adj_source Rp hp)
  have hnv := (unitDistanceGraph A).adj_symm (case13Row_adj_source Rn hn)
  have hpPoint : (p.1 : Vertex A) = (P.next⁻¹ i).1 := by
    exact congrArg Subtype.val hprev
  have hnPoint : (n.1 : Vertex A) = (P.next i).1 := by
    exact congrArg Subtype.val hnext
  exact Erdos957CaseClassification.not_both_cyclic_neighbors_adjacent_to_middle
    hA P W i s.property v (by simpa [i, sourceIndex] using hsv)
      (by simpa [hpPoint] using hpv) (by simpa [hnPoint] using hnv)

/-- Complete arithmetic classification of two positions in the seven-window.
The first three alternatives are the equality cases, the next four put one
position three steps from the center, and the final twelve list the only
remaining ordered distinct pairs.  This small theorem keeps the geometric
dispatch below deterministic and within the default heartbeat budget. -/
private lemma finSeven_pair_cases (j k : Fin 7) :
    j = 3 ∨ k = 3 ∨ j = k ∨
    j = 0 ∨ j = 6 ∨ k = 0 ∨ k = 6 ∨
    (j = 1 ∧ k = 2) ∨ (j = 1 ∧ k = 4) ∨
    (j = 1 ∧ k = 5) ∨ (j = 2 ∧ k = 1) ∨
    (j = 2 ∧ k = 4) ∨ (j = 2 ∧ k = 5) ∨
    (j = 4 ∧ k = 1) ∨ (j = 4 ∧ k = 2) ∨
    (j = 4 ∧ k = 5) ∨ (j = 5 ∧ k = 1) ∨
    (j = 5 ∧ k = 2) ∨ (j = 5 ∧ k = 4) := by
  fin_cases j <;> fin_cases k <;> simp

/-- Three Case 1/3 source rows in one genuine seven-window cannot select the
same target.  This is the complete finite offset dispatch for the 1/3-only
part of `NoThreeRoleCollisionWitnesses.no_three_in_window`. -/
theorem no_three_case13_in_window
    (hA : IsOneSeparated A) {a b c : Source P W}
    (Ra : Case13Row (F := F) a) (Rb : Case13Row (F := F) b)
    (Rc : Case13Row (F := F) c) {v : Vertex A}
    (ha : 0 < Ra.tokens v) (hb : 0 < Rb.tokens v)
    (hc : 0 < Rc.tokens v)
    (hbWindow : b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1))
    (hcWindow : c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  let ia := sourceIndex P W a.1 a.property
  rcases Finset.mem_image.mp hbWindow with ⟨jb, hjb, hjbEq⟩
  rcases Finset.mem_image.mp hcWindow with ⟨jc, hjc, hjcEq⟩
  have hib : sourceIndex P W b.1 b.property = sevenShift P.next jb ia := by
    apply Subtype.ext
    exact hjbEq.symm
  have hic : sourceIndex P W c.1 c.property = sevenShift P.next jc ia := by
    apply Subtype.ext
    exact hjcEq.symm
  rcases finSeven_pair_cases jb jc with
      hj | hk | hjk | hj | hj | hk | hk |
      hjk | hjk | hjk | hjk | hjk | hjk |
      hjk | hjk | hjk | hjk | hjk | hjk
  · subst jb
    apply hab
    apply Subtype.ext
    simpa [ia, sourceIndex] using (congrArg Subtype.val hib).symm
  · subst jc
    apply hac
    apply Subtype.ext
    simpa [ia, sourceIndex] using (congrArg Subtype.val hic).symm
  · subst jc
    apply hbc
    apply Subtype.ext
    simpa [sourceIndex] using congrArg Subtype.val (hib.trans hic.symm)
  · subst jb
    exact no_case13_common_target_third_predecessor Ra Rb ha hb
      (by simpa [ia] using hib)
  · subst jb
    exact no_case13_common_target_third_successor Ra Rb ha hb
      (by simpa [ia] using hib)
  · subst jc
    exact no_case13_common_target_third_predecessor Ra Rc ha hc
      (by simpa [ia] using hic)
  · subst jc
    exact no_case13_common_target_third_successor Ra Rc ha hc
      (by simpa [ia] using hic)
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_prev_self_next hA Rb Rc Ra hb hc ha
      (by simp only [hib, hic]; simp [pow_succ])
      (by simp only [hic]; simp [ia])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_third_successor Rb Rc hb hc
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_fourth_successor Rb Rc hb hc
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_prev_self_next hA Rc Rb Ra hc hb ha
      (by simp only [hib, hic]; simp [pow_succ])
      (by simp only [hib]; simp [ia])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_prev_self_next hA Rb Ra Rc hb ha hc
      (by simpa [ia] using hib) (by simpa [ia] using hic)
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_third_successor Rb Rc hb hc
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_third_successor Rc Rb hc hb
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_prev_self_next hA Rc Ra Rb hc ha hb
      (by simpa [ia] using hic) (by simpa [ia] using hib)
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_prev_self_next hA Ra Rb Rc ha hb hc
      (by simp only [hib]; simp [ia])
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_fourth_successor Rc Rb hc hb
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_third_successor Rc Rb hc hb
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_case13_common_target_prev_self_next hA Ra Rc Rb ha hc hb
      (by simp only [hic]; simp [ia])
      (by simp only [hib, hic]; simp [pow_succ])

/-! The same finite theorem depends only on the three actual unit
incidences.  This is the form consumed by mixed realized roles whose
recipient is a direct unit neighbour of its source. -/

lemma no_common_unit_target_third_successor
    (F : P.FlatAlignedFrameData) {s t : Source P W} {v : Vertex A}
    (hs : (unitDistanceGraph A).Adj s.1 v)
    (ht : (unitDistanceGraph A).Adj t.1 v)
    (hst : sourceIndex P W t.1 t.property =
      (P.next ^ 3) (sourceIndex P W s.1 s.property)) : False := by
  have hfar := Erdos957GeometryLocalityBridge.dist_third_successor_gt_two
    F (sourceIndex P W s.1 s.property)
      (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
  have hdist : dist (s.1 : Point) (t.1 : Point) ≤ 2 := by
    calc
      _ ≤ dist (s.1 : Point) (v : Point) + dist (v : Point) (t.1 : Point) :=
        dist_triangle _ _ _
      _ = 2 := by
        rw [show dist (s.1 : Point) (v : Point) = 1 by
              simpa [unitDistanceGraph] using hs,
            show dist (v : Point) (t.1 : Point) = 1 by
              simpa [unitDistanceGraph, dist_comm] using ht]
        norm_num
  have hpoints :
      ((((P.next ^ 3) (sourceIndex P W s.1 s.property)).1 : Vertex A) : Point) =
        (t.1 : Point) := by
    simpa [sourceIndex] using congrArg (fun x : {p // p ∈ P.H} ↦
      (x.1 : Point)) hst.symm
  rw [hpoints] at hfar
  exact (not_lt_of_ge hdist) hfar

lemma no_common_unit_target_third_predecessor
    (F : P.FlatAlignedFrameData) {s t : Source P W} {v : Vertex A}
    (hs : (unitDistanceGraph A).Adj s.1 v)
    (ht : (unitDistanceGraph A).Adj t.1 v)
    (hst : sourceIndex P W t.1 t.property =
      ((P.next⁻¹) ^ 3) (sourceIndex P W s.1 s.property)) : False := by
  have hfar := Erdos957GeometryLocalityBridge.dist_third_predecessor_gt_two
    F (sourceIndex P W s.1 s.property)
      (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
  have hdist : dist (s.1 : Point) (t.1 : Point) ≤ 2 := by
    calc
      _ ≤ dist (s.1 : Point) (v : Point) + dist (v : Point) (t.1 : Point) :=
        dist_triangle _ _ _
      _ = 2 := by
        rw [show dist (s.1 : Point) (v : Point) = 1 by
              simpa [unitDistanceGraph] using hs,
            show dist (v : Point) (t.1 : Point) = 1 by
              simpa [unitDistanceGraph, dist_comm] using ht]
        norm_num
  have hpoints :
      (((((P.next⁻¹) ^ 3) (sourceIndex P W s.1 s.property)).1 : Vertex A) : Point) =
        (t.1 : Point) := by
    simpa [sourceIndex] using congrArg (fun x : {p // p ∈ P.H} ↦
      (x.1 : Point)) hst.symm
  rw [hpoints] at hfar
  exact (not_lt_of_ge hdist) hfar

lemma no_three_consecutive_common_unit_target
    (hA : IsOneSeparated A) {p s n : Source P W} {v : Vertex A}
    (hp : (unitDistanceGraph A).Adj p.1 v)
    (hs : (unitDistanceGraph A).Adj s.1 v)
    (hn : (unitDistanceGraph A).Adj n.1 v)
    (hprev : sourceIndex P W p.1 p.property =
      P.next⁻¹ (sourceIndex P W s.1 s.property))
    (hnext : sourceIndex P W n.1 n.property =
      P.next (sourceIndex P W s.1 s.property)) : False := by
  let i := sourceIndex P W s.1 s.property
  have hpPoint : (p.1 : Vertex A) = (P.next⁻¹ i).1 :=
    congrArg Subtype.val hprev
  have hnPoint : (n.1 : Vertex A) = (P.next i).1 :=
    congrArg Subtype.val hnext
  exact Erdos957CaseClassification.not_both_cyclic_neighbors_adjacent_to_middle
    hA P W i s.property v (by simpa [i, sourceIndex] using hs)
      (by simpa [hpPoint] using (unitDistanceGraph A).adj_symm hp)
      (by simpa [hnPoint] using (unitDistanceGraph A).adj_symm hn)

/-- Three pairwise distinct source vertices in one genuine seven-window
cannot all be unit adjacent to one target. -/
theorem no_three_common_unit_target_in_window
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    {a b c : Source P W} {v : Vertex A}
    (ha : (unitDistanceGraph A).Adj a.1 v)
    (hb : (unitDistanceGraph A).Adj b.1 v)
    (hc : (unitDistanceGraph A).Adj c.1 v)
    (hbWindow : b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1))
    (hcWindow : c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  let ia := sourceIndex P W a.1 a.property
  rcases Finset.mem_image.mp hbWindow with ⟨jb, _, hjbEq⟩
  rcases Finset.mem_image.mp hcWindow with ⟨jc, _, hjcEq⟩
  have hib : sourceIndex P W b.1 b.property = sevenShift P.next jb ia := by
    apply Subtype.ext
    exact hjbEq.symm
  have hic : sourceIndex P W c.1 c.property = sevenShift P.next jc ia := by
    apply Subtype.ext
    exact hjcEq.symm
  rcases finSeven_pair_cases jb jc with
      hj | hk | hjk | hj | hj | hk | hk |
      hjk | hjk | hjk | hjk | hjk | hjk |
      hjk | hjk | hjk | hjk | hjk | hjk
  · subst jb
    apply hab
    apply Subtype.ext
    simpa [ia, sourceIndex] using (congrArg Subtype.val hib).symm
  · subst jc
    apply hac
    apply Subtype.ext
    simpa [ia, sourceIndex] using (congrArg Subtype.val hic).symm
  · subst jc
    apply hbc
    apply Subtype.ext
    simpa [sourceIndex] using congrArg Subtype.val (hib.trans hic.symm)
  · subst jb
    exact no_common_unit_target_third_predecessor (F := F) ha hb
      (by simpa [ia] using hib)
  · subst jb
    exact no_common_unit_target_third_successor (F := F) ha hb
      (by simpa [ia] using hib)
  · subst jc
    exact no_common_unit_target_third_predecessor (F := F) ha hc
      (by simpa [ia] using hic)
  · subst jc
    exact no_common_unit_target_third_successor (F := F) ha hc
      (by simpa [ia] using hic)
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_three_consecutive_common_unit_target hA hb hc ha
      (by simp only [hib, hic]; simp [pow_succ])
      (by simp only [hic]; simp [ia])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_common_unit_target_third_successor (F := F) hb hc
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    have h4 := Erdos957GeometryLocalityBridge.dist_fourth_successor_gt_two
      F (sourceIndex P W b.1 b.property)
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W b)
    have hdist : dist (b.1 : Point) (c.1 : Point) ≤ 2 := by
      calc
        _ ≤ dist (b.1 : Point) (v : Point) + dist (v : Point) (c.1 : Point) :=
          dist_triangle _ _ _
        _ = 2 := by
          rw [show dist (b.1 : Point) (v : Point) = 1 by
                simpa [unitDistanceGraph] using hb,
              show dist (v : Point) (c.1 : Point) = 1 by
                simpa [unitDistanceGraph, dist_comm] using hc]
          norm_num
    have hrel : sourceIndex P W c.1 c.property =
        (P.next ^ 4) (sourceIndex P W b.1 b.property) := by
      simp only [hib, hic]
      simp [pow_succ]
    have hpoints :
        ((((P.next ^ 4) (sourceIndex P W b.1 b.property)).1 : Vertex A) : Point) =
          (c.1 : Point) := by
      simpa [sourceIndex] using congrArg (fun x : {p // p ∈ P.H} ↦
        (x.1 : Point)) hrel.symm
    rw [hpoints] at h4
    exact (not_lt_of_ge hdist) h4
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_three_consecutive_common_unit_target hA hc hb ha
      (by simp only [hib, hic]; simp [pow_succ])
      (by simp only [hib]; simp [ia])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_three_consecutive_common_unit_target hA hb ha hc
      (by simpa [ia] using hib) (by simpa [ia] using hic)
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_common_unit_target_third_successor (F := F) hb hc
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_common_unit_target_third_successor (F := F) hc hb
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_three_consecutive_common_unit_target hA hc ha hb
      (by simpa [ia] using hic) (by simpa [ia] using hib)
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_three_consecutive_common_unit_target hA ha hb hc
      (by simp only [hib]; simp [ia])
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    have h4 := Erdos957GeometryLocalityBridge.dist_fourth_successor_gt_two
      F (sourceIndex P W c.1 c.property)
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W c)
    have hdist : dist (c.1 : Point) (b.1 : Point) ≤ 2 := by
      calc
        _ ≤ dist (c.1 : Point) (v : Point) + dist (v : Point) (b.1 : Point) :=
          dist_triangle _ _ _
        _ = 2 := by
          rw [show dist (c.1 : Point) (v : Point) = 1 by
                simpa [unitDistanceGraph] using hc,
              show dist (v : Point) (b.1 : Point) = 1 by
                simpa [unitDistanceGraph, dist_comm] using hb]
          norm_num
    have hrel : sourceIndex P W b.1 b.property =
        (P.next ^ 4) (sourceIndex P W c.1 c.property) := by
      simp only [hib, hic]
      simp [pow_succ]
    have hpoints :
        ((((P.next ^ 4) (sourceIndex P W c.1 c.property)).1 : Vertex A) : Point) =
          (b.1 : Point) := by
      simpa [sourceIndex] using congrArg (fun x : {p // p ∈ P.H} ↦
        (x.1 : Point)) hrel.symm
    rw [hpoints] at h4
    exact (not_lt_of_ge hdist) h4
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_common_unit_target_third_successor (F := F) hc hb
      (by simp only [hib, hic]; simp [pow_succ])
  · rcases hjk with ⟨rfl, rfl⟩
    exact no_three_consecutive_common_unit_target hA ha hc hb
      (by simp only [hic]; simp [ia])
      (by simp only [hib, hic]; simp [pow_succ])

/-! ## Definitional connection to the selected realized-row family -/

/-- Choose the actual formula row itself, rather than recovering an
unrelated inhabitant through `Nonempty.some`. -/
def localCasesOfRealizedRows
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart) :
    HasLocalCases P W F.chart :=
  fun u hu ↦ (rows u hu).localCase

/-- Recover the exact enriched Case-3 constructor from its erased global
case tag.  This is the bridge needed by the role-sensitive Case-3 collision
lemmas; no formula data are reconstructed from the tag. -/
lemma isCase3Row_of_caseTag_eq_three
    {source : {p // p ∈ P.H}}
    (R : Erdos957CaseClassification.RealizedSourceRow P F.chart source)
    (h : R.localCase.caseTag = .three) :
    Erdos957Case3SameSide.IsCase3Row R := by
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
      simp [Erdos957CaseClassification.RealizedSourceRow.localCase,
        Erdos957CaseClassification.PairCases.Case1ActualRow.localCase,
        LocalCase.caseTag] at h
  | case2 middle hdegree htwo hmiddleNot T normalized row =>
      simp [Erdos957CaseClassification.RealizedSourceRow.localCase,
        Erdos957CaseClassification.ActualCase24Rows.Case2ActualRow.localCase,
        LocalCase.caseTag] at h
  | case3 middle hdegree hone middleCoord row hmiddle =>
      exact ⟨middle, hdegree, hone, middleCoord, row, hmiddle, rfl⟩
  | case4 middle hdegree htwo T normalized row hmiddle =>
      cases row <;>
        simp [Erdos957CaseClassification.RealizedSourceRow.localCase,
          Erdos957CaseClassification.ActualCase24Rows.Case4ActualRow.localCase,
          LocalCase.caseTag] at h

/-- Forget the case-classification fields of a realized Case 1/3 source
while retaining exactly the formulas used by the checked collision lemma. -/
def realizedCase13Row?
    {source : {p // p ∈ P.H}} :
    Erdos957CaseClassification.RealizedSourceRow P F.chart source →
      Option (ActualRow (P := P) (C := F.chart) source)
  | .case1 _ _ _ middle _ _ hunit row =>
      some (.case1 middle ⟨row, hunit⟩)
  | .case3 _ _ _ middle row _ =>
      some (.case3 middle row)
  | .case2 _ _ _ _ _ _ _ => none
  | .case4 _ _ _ _ _ _ _ => none

lemma realizedCase13Row_localCase
    {source : {p // p ∈ P.H}}
    {R : Erdos957CaseClassification.RealizedSourceRow P F.chart source}
    {Q : ActualRow (P := P) (C := F.chart) source}
    (hQ : realizedCase13Row? (F := F) R = some Q) :
    R.localCase = Q.localCase := by
  cases R <;> simp [realizedCase13Row?] at hQ
  all_goals cases hQ
  all_goals rfl

/-- The checked Case 1/3 finite dispatch now applies directly to the rows
selected by the honest dependent-data `HasRealizedSourceRows` interface. -/
theorem no_three_selected_realized_case13_in_window
    (hA : IsOneSeparated A)
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart)
    {a b c : Source P W} {v : Vertex A}
    (Qa : Case13Row (F := F) a) (Qb : Case13Row (F := F) b)
    (Qc : Case13Row (F := F) c)
    (haCase : realizedCase13Row? (F := F) (rows a.1 a.property) = some Qa)
    (hbCase : realizedCase13Row? (F := F) (rows b.1 b.property) = some Qb)
    (hcCase : realizedCase13Row? (F := F) (rows c.1 c.property) = some Qc)
    (ha : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) a v)
    (hb : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) b v)
    (hc : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) c v)
    (hbWindow : b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1))
    (hcWindow : c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  have hQa := realizedCase13Row_localCase (F := F) haCase
  have hQb := realizedCase13Row_localCase (F := F) hbCase
  have hQc := realizedCase13Row_localCase (F := F) hcCase
  apply no_three_case13_in_window hA Qa Qb Qc
  · simpa [sourceTokens, selectedCase, localCasesOfRealizedRows,
      ActualRow.tokens, hQa] using ha
  · simpa [sourceTokens, selectedCase, localCasesOfRealizedRows,
      ActualRow.tokens, hQb] using hb
  · simpa [sourceTokens, selectedCase, localCasesOfRealizedRows,
      ActualRow.tokens, hQc] using hc
  · exact hbWindow
  · exact hcWindow
  · exact hab
  · exact hac
  · exact hbc

/-! ## Minimal mixed-role interface

The retained formulas show that every role except the Case-2 secondary and
the Case-4 split-right recipient is a direct unit neighbour of its source.
Thus the checked common-unit theorem disposes of every all-direct triple.

The exceptional interface below deliberately asks for a *finite, role-aware
three-arrival exclusion*.  It does not assert the stronger (and generally
unjustified) statement that an exceptional recipient determines its source.
In particular, the two competing arrivals are supplied with their own exact
formula descriptors; the geometric leaves can therefore dispatch on the
left/right role retained by each constructor. -/

def IsExceptionalSecondaryRole :
    Erdos957CaseClassification.PairCases.TargetRoleName → Prop
  | .case2Secondary | .case4SplitRight => True
  | _ => False

structure SecondaryRoleCollisionKernels
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart) where
  /-- Finite left/right role dispatch anchored at a Case-2 secondary hit. -/
  case2_secondary_no_three : ∀ {s t u : Source P W} {v : Vertex A}
    (Ds : Erdos957CaseClassification.RealizedPositiveTarget
      (rows s.1 s.property) v)
    (Dt : Erdos957CaseClassification.RealizedPositiveTarget
      (rows t.1 t.property) v)
    (Du : Erdos957CaseClassification.RealizedPositiveTarget
      (rows u.1 u.property) v),
    Ds.role = .case2Secondary →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False
  /-- Reflection-invariant finite role dispatch anchored at the pair-coherent
  Case-4 low/high split-right recipient. -/
  case4_split_right_no_three : ∀ {s t u : Source P W} {v : Vertex A}
    (Ds : Erdos957CaseClassification.RealizedPositiveTarget
      (rows s.1 s.property) v)
    (Dt : Erdos957CaseClassification.RealizedPositiveTarget
      (rows t.1 t.property) v)
    (Du : Erdos957CaseClassification.RealizedPositiveTarget
      (rows u.1 u.property) v),
    Ds.role = .case4SplitRight →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False

namespace SecondaryRoleCollisionKernels

variable {rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart}

lemma exceptional_no_three
    (K : SecondaryRoleCollisionKernels (F := F) rows)
    {s t u : Source P W} {v : Vertex A}
    (Ds : Erdos957CaseClassification.RealizedPositiveTarget
      (rows s.1 s.property) v)
    (Dt : Erdos957CaseClassification.RealizedPositiveTarget
      (rows t.1 t.property) v)
    (Du : Erdos957CaseClassification.RealizedPositiveTarget
      (rows u.1 u.property) v)
    (hD : IsExceptionalSecondaryRole Ds.role)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) : False := by
  have hcases : Ds.role = .case2Secondary ∨ Ds.role = .case4SplitRight := by
    by_cases hcase2 : Ds.role = .case2Secondary
    · exact Or.inl hcase2
    · by_cases hcase4 : Ds.role = .case4SplitRight
      · exact Or.inr hcase4
      · exfalso
        cases hrole : Ds.role <;>
          simp_all [IsExceptionalSecondaryRole]
  rcases hcases with hcase2 | hcase4
  · exact K.case2_secondary_no_three Ds Dt Du hcase2 htWindow huWindow
      hst hsu htu
  · exact K.case4_split_right_no_three Ds Dt Du hcase4 htWindow huWindow
      hst hsu htu

private lemma ne_case2Secondary_of_not_exceptional
    {role : Erdos957CaseClassification.PairCases.TargetRoleName}
    (h : ¬ IsExceptionalSecondaryRole role) :
    role ≠ .case2Secondary := by
  intro hr
  subst role
  exact h trivial

private lemma ne_case4SplitRight_of_not_exceptional
    {role : Erdos957CaseClassification.PairCases.TargetRoleName}
    (h : ¬ IsExceptionalSecondaryRole role) :
    role ≠ .case4SplitRight := by
  intro hr
  subst role
  exact h trivial

/-- The two honest exceptional-role uniqueness kernels, together with
formula-derived direct incidences, assemble the side-free no-three witness
consumed by production `CollisionGlue`. -/
noncomputable def noThreeRoleCollisionWitnesses
    (hA : IsOneSeparated A)
    (locality : SourceLocalityCertificates P W F)
    (K : SecondaryRoleCollisionKernels (F := F) rows) :
    NoThreeRoleCollisionWitnesses P W F
      (localCasesOfRealizedRows (F := F) rows) where
  locality := locality
  no_three_in_window := by
    intro a b c v ha hb hc hbWindow hcWindow hab hac hbc
    have haRow : 0 < (rows a.1 a.property).localCase.tokens v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using ha
    have hbRow : 0 < (rows b.1 b.property).localCase.tokens v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using hb
    have hcRow : 0 < (rows c.1 c.property).localCase.tokens v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using hc
    obtain ⟨Da⟩ := (rows a.1 a.property).positive_target_role haRow
    obtain ⟨Db⟩ := (rows b.1 b.property).positive_target_role hbRow
    obtain ⟨Dc⟩ := (rows c.1 c.property).positive_target_role hcRow
    by_cases hsa : IsExceptionalSecondaryRole Da.role
    · exact K.exceptional_no_three Da Db Dc hsa hbWindow hcWindow
        hab hac hbc
    · by_cases hsb : IsExceptionalSecondaryRole Db.role
      · have haWindow := locality.competing_source_in_window hb ha
        have hcFromBWindow := locality.competing_source_in_window hb hc
        exact K.exceptional_no_three Db Da Dc hsb haWindow hcFromBWindow
          hab.symm hbc hac
      · by_cases hsc : IsExceptionalSecondaryRole Dc.role
        · have haWindow := locality.competing_source_in_window hc ha
          have hbFromCWindow := locality.competing_source_in_window hc hb
          exact K.exceptional_no_three Dc Da Db hsc haWindow hbFromCWindow
            hac.symm hbc.symm hab
        · exact no_three_common_unit_target_in_window hA F
            (Da.direct_target_adj
              (ne_case2Secondary_of_not_exceptional hsa)
              (ne_case4SplitRight_of_not_exceptional hsa))
            (Db.direct_target_adj
              (ne_case2Secondary_of_not_exceptional hsb)
              (ne_case4SplitRight_of_not_exceptional hsb))
            (Dc.direct_target_adj
              (ne_case2Secondary_of_not_exceptional hsc)
              (ne_case4SplitRight_of_not_exceptional hsc))
            hbWindow hcWindow hab hac hbc

end SecondaryRoleCollisionKernels

/-! ## Two-sided pairwise collision interface

The production transfer theorem uses a two-colouring of positive arrivals,
not the stronger auxiliary no-three statement above.  The declarations in
this section connect the reflection-correct, formula-derived arrival
descriptor to that production interface.  The ten fields of
`RealizedSameSideKernels` are deliberately indexed by the ten unordered
case pairs: they are geometric pair statements, not an incoming-sum or
capacity assumption. -/

/-- Boolean encoding used by production `RoleCollisionWitnesses`. -/
def arrivalAssociationBool :
    Erdos957CaseClassification.ArrivalAssociation → Bool
  | .fromPrevious => false
  | .fromNext => true

lemma arrivalAssociationBool_injective :
    Function.Injective arrivalAssociationBool := by
  intro a b h
  cases a <;> cases b <;> simp_all [arrivalAssociationBool]

/-- One selected positive arrival, bundled with both its exact formula role
and the checked side/weight certificate derived from that role. -/
structure RealizedArrivalAt
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart)
    (s : Source P W) (v : Vertex A) where
  positive : 0 < (rows s.1 s.property).localCase.tokens v
  target : Erdos957CaseClassification.RealizedPositiveTarget
    (rows s.1 s.property) v
  descriptor : Erdos957CaseClassification.RealizedArrivalDescriptor
    (rows s.1 s.property) target.role target.target

/-- A Case-3 middle-role collision identifies the emitting source outright.
This closes middle/middle and both middle/secondary subbranches before any
cyclic-offset or side analysis. -/
theorem case3_source_eq_of_middle_role
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (hsTag : (rows s.1 s.property).localCase.caseTag = .three)
    (htTag : (rows t.1 t.property).localCase.caseTag = .three)
    (hmiddle : S.target.role = .case3Middle ∨
      T.target.role = .case3Middle) : s = t := by
  have hsRow := isCase3Row_of_caseTag_eq_three (F := F)
    (rows s.1 s.property) hsTag
  have htRow := isCase3Row_of_caseTag_eq_three (F := F)
    (rows t.1 t.property) htTag
  have hsource :=
    Erdos957Case3SameSide.source_eq_of_case3_collision_of_middle_role
      S.target T.target hsRow htRow hmiddle
  apply Subtype.ext
  simpa [sourceIndex] using congrArg Subtype.val hsource

/-- The descriptor exists for the very same selected row used by the global
transfer; no unrelated `Nonempty.some` row is introduced. -/
noncomputable def realizedArrivalAtOfPositive
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart)
    (s : Source P W) (v : Vertex A)
    (h : 0 < (rows s.1 s.property).localCase.tokens v) :
    RealizedArrivalAt (F := F) rows s v := by
  let D := Classical.choice
    ((rows s.1 s.property).positive_target_role h)
  let E := Classical.choice D.arrivalDescriptor
  exact ⟨h, D, E⟩

/-- Bundle a previously extracted realized target with the positive-token and
arrival-certificate data expected by the pairwise collision layer.  Unlike
`realizedArrivalAtOfPositive`, this keeps the caller's exact target witness. -/
noncomputable def realizedArrivalAtOfTarget
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart)
    (s : Source P W) (v : Vertex A)
    (D : Erdos957CaseClassification.RealizedPositiveTarget
      (rows s.1 s.property) v) :
    RealizedArrivalAt (F := F) rows s v := by
  refine ⟨?_, D, Classical.choice D.arrivalDescriptor⟩
  rw [D.token_eq_roleWeight]
  cases (rows s.1 s.property).roleWeight D.role <;>
    simp [Erdos957CaseClassification.ArrivalWeight.tokens]

/-- Total side function.  Its zero-arrival value is irrelevant; on a
positive arrival it is definitionally the side of the checked descriptor. -/
noncomputable def realizedArrivalSide
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart)
    (s : Source P W) (v : Vertex A) : Bool :=
  if h : 0 < (rows s.1 s.property).localCase.tokens v then
    arrivalAssociationBool
      (realizedArrivalAtOfPositive (F := F) rows s v h).descriptor.association
  else false

lemma realizedArrivalSide_of_positive
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart)
    (s : Source P W) (v : Vertex A)
    (h : 0 < (rows s.1 s.property).localCase.tokens v) :
    realizedArrivalSide (F := F) rows s v =
      arrivalAssociationBool
        (realizedArrivalAtOfPositive (F := F) rows s v h).descriptor.association := by
  simp [realizedArrivalSide, h]

/-- One of the ten unordered case-pair leaves.  Besides the two exact
formula descriptors it assumes only the genuine seven-window relation and
equality of their reflection-correct sides. -/
def RealizedSameSidePairKernel
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart)
    (first second : Erdos957Overcharge.CaseNumber) : Prop :=
  ∀ {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v),
    (rows s.1 s.property).localCase.caseTag = first →
    (rows t.1 t.property).localCase.caseTag = second →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    S.descriptor.association = T.descriptor.association → s = t

/-- The ten honest finite same-side geometry targets.  Each field is a
formula/offset theorem for one unordered pair of Dumitrescu cases. -/
structure RealizedSameSideKernels
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart) where
  one_one : RealizedSameSidePairKernel (F := F) rows .one .one
  one_two : RealizedSameSidePairKernel (F := F) rows .one .two
  one_three : RealizedSameSidePairKernel (F := F) rows .one .three
  one_four : RealizedSameSidePairKernel (F := F) rows .one .four
  two_two : RealizedSameSidePairKernel (F := F) rows .two .two
  two_three : RealizedSameSidePairKernel (F := F) rows .two .three
  two_four : RealizedSameSidePairKernel (F := F) rows .two .four
  three_three : RealizedSameSidePairKernel (F := F) rows .three .three
  three_four : RealizedSameSidePairKernel (F := F) rows .three .four
  four_four : RealizedSameSidePairKernel (F := F) rows .four .four

/-- Role-level leaves from which all ten tag-pair kernels are obtained.
The first field is the common unit-incidence/formula theorem for the eight
direct roles.  The other two fields are precisely the only roles which are
not unit-adjacent to their emitting source. -/
structure RoleAnchoredSameSideKernels
    (rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart) where
  direct_direct : ∀ {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v),
    Erdos957CaseClassification.IsDirectTargetRole S.target.role →
    Erdos957CaseClassification.IsDirectTargetRole T.target.role →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    S.descriptor.association = T.descriptor.association → s = t
  case2_secondary : ∀ {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v),
    S.target.role = .case2Secondary →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    S.descriptor.association = T.descriptor.association → s = t
  case4_split_right : ∀ {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v),
    S.target.role = .case4SplitRight →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    S.descriptor.association = T.descriptor.association → s = t

namespace RoleAnchoredSameSideKernels

variable {rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart}

private lemma direct_of_not_exceptional
    {role : Erdos957CaseClassification.PairCases.TargetRoleName}
    (h2 : role ≠ .case2Secondary) (h4 : role ≠ .case4SplitRight) :
    Erdos957CaseClassification.IsDirectTargetRole role := by
  cases hrole : role <;>
    simp_all [Erdos957CaseClassification.IsDirectTargetRole]

/-- Reflection-safe role dispatch.  If the exceptional role occurs on the
second source, metric locality supplies the reverse seven-window before the
corresponding anchored leaf is invoked. -/
theorem same_side_source_unique
    (locality : SourceLocalityCertificates P W F)
    (K : RoleAnchoredSameSideKernels (F := F) rows)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hassoc : S.descriptor.association = T.descriptor.association) : s = t := by
  have hsPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) s v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using S.positive
  have htPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) t v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using T.positive
  have hsFromTWindow := locality.competing_source_in_window htPos hsPos
  by_cases hs2 : S.target.role = .case2Secondary
  · exact K.case2_secondary S T hs2 htWindow hassoc
  · by_cases ht2 : T.target.role = .case2Secondary
    · exact (K.case2_secondary T S ht2 hsFromTWindow hassoc.symm).symm
    · by_cases hs4 : S.target.role = .case4SplitRight
      · exact K.case4_split_right S T hs4 htWindow hassoc
      · by_cases ht4 : T.target.role = .case4SplitRight
        · exact (K.case4_split_right T S ht4 hsFromTWindow hassoc.symm).symm
        · exact K.direct_direct S T
            (direct_of_not_exceptional hs2 hs4)
            (direct_of_not_exceptional ht2 ht4) htWindow hassoc

/-- Three two-valued arrival associations contain an equal pair. -/
private lemma three_associations_have_equal_pair
    (a b c : Erdos957CaseClassification.ArrivalAssociation) :
    a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> simp

/-- The pairwise formula kernels imply the smaller side-free exceptional
triple interface.  In the third pigeonhole branch, metric locality supplies
the genuine window from the second competitor to the third. -/
noncomputable def secondaryRoleCollisionKernels
    (locality : SourceLocalityCertificates P W F)
    (K : RoleAnchoredSameSideKernels (F := F) rows) :
    SecondaryRoleCollisionKernels (F := F) rows where
  case2_secondary_no_three := by
    intro s t u v Ds Dt Du hsRole htWindow huWindow hst hsu htu
    let S := realizedArrivalAtOfTarget (F := F) rows s v Ds
    let T := realizedArrivalAtOfTarget (F := F) rows t v Dt
    let U := realizedArrivalAtOfTarget (F := F) rows u v Du
    have htPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) rows) t v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using T.positive
    have huPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) rows) u v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using U.positive
    rcases three_associations_have_equal_pair S.descriptor.association
        T.descriptor.association U.descriptor.association with h | h | h
    · exact hst (K.same_side_source_unique locality S T htWindow h)
    · exact hsu (K.same_side_source_unique locality S U huWindow h)
    · have huFromTWindow := locality.competing_source_in_window htPos huPos
      exact htu (K.same_side_source_unique locality T U huFromTWindow h)
  case4_split_right_no_three := by
    intro s t u v Ds Dt Du hsRole htWindow huWindow hst hsu htu
    let S := realizedArrivalAtOfTarget (F := F) rows s v Ds
    let T := realizedArrivalAtOfTarget (F := F) rows t v Dt
    let U := realizedArrivalAtOfTarget (F := F) rows u v Du
    have htPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) rows) t v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using T.positive
    have huPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) rows) u v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using U.positive
    rcases three_associations_have_equal_pair S.descriptor.association
        T.descriptor.association U.descriptor.association with h | h | h
    · exact hst (K.same_side_source_unique locality S T htWindow h)
    · exact hsu (K.same_side_source_unique locality S U huWindow h)
    · have huFromTWindow := locality.competing_source_in_window htPos huPos
      exact htu (K.same_side_source_unique locality T U huFromTWindow h)

/-- The three exact role leaves fill each of the ten unordered case-pair
fields without adding a capacity or incoming-sum premise. -/
def realizedSameSideKernels
    (locality : SourceLocalityCertificates P W F)
    (K : RoleAnchoredSameSideKernels (F := F) rows) :
    RealizedSameSideKernels (F := F) rows where
  one_one := by intro s t v S T _ _ hw hs; exact K.same_side_source_unique locality S T hw hs
  one_two := by intro s t v S T _ _ hw hs; exact K.same_side_source_unique locality S T hw hs
  one_three := by intro s t v S T _ _ hw hs; exact K.same_side_source_unique locality S T hw hs
  one_four := by intro s t v S T _ _ hw hs; exact K.same_side_source_unique locality S T hw hs
  two_two := by intro s t v S T _ _ hw hs; exact K.same_side_source_unique locality S T hw hs
  two_three := by intro s t v S T _ _ hw hs; exact K.same_side_source_unique locality S T hw hs
  two_four := by intro s t v S T _ _ hw hs; exact K.same_side_source_unique locality S T hw hs
  three_three := by intro s t v S T _ _ hw hs; exact K.same_side_source_unique locality S T hw hs
  three_four := by intro s t v S T _ _ hw hs; exact K.same_side_source_unique locality S T hw hs
  four_four := by intro s t v S T _ _ hw hs; exact K.same_side_source_unique locality S T hw hs

end RoleAnchoredSameSideKernels

namespace RealizedSameSideKernels

variable {rows : Erdos957CaseClassification.HasRealizedSourceRows P W F.chart}

/-- Exhaust the sixteen ordered tag pairs using the ten unordered kernels;
the reverse branches obtain their genuine reverse window from metric
locality. -/
theorem same_side_unique_in_window
    (locality : SourceLocalityCertificates P W F)
    (K : RealizedSameSideKernels (F := F) rows)
    {s t : Source P W} {v : Vertex A}
    (hs : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) s v)
    (ht : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) t v)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hside : realizedArrivalSide (F := F) rows s v =
      realizedArrivalSide (F := F) rows t v) : s = t := by
  have hsRow : 0 < (rows s.1 s.property).localCase.tokens v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using hs
  have htRow : 0 < (rows t.1 t.property).localCase.tokens v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using ht
  let S := realizedArrivalAtOfPositive (F := F) rows s v hsRow
  let T := realizedArrivalAtOfPositive (F := F) rows t v htRow
  have hside' : arrivalAssociationBool S.descriptor.association =
      arrivalAssociationBool T.descriptor.association := by
    rw [realizedArrivalSide_of_positive (F := F) rows s v hsRow,
      realizedArrivalSide_of_positive (F := F) rows t v htRow] at hside
    simpa [S, T] using hside
  have hassoc : S.descriptor.association = T.descriptor.association :=
    arrivalAssociationBool_injective hside'
  have hsFromTWindow := locality.competing_source_in_window ht hs
  cases hsEq : (rows s.1 s.property).localCase.caseTag <;>
    cases htEq : (rows t.1 t.property).localCase.caseTag
  · exact K.one_one S T hsEq htEq htWindow hassoc
  · exact K.one_two S T hsEq htEq htWindow hassoc
  · exact K.one_three S T hsEq htEq htWindow hassoc
  · exact K.one_four S T hsEq htEq htWindow hassoc
  · exact (K.one_two T S htEq hsEq hsFromTWindow hassoc.symm).symm
  · exact K.two_two S T hsEq htEq htWindow hassoc
  · exact K.two_three S T hsEq htEq htWindow hassoc
  · exact K.two_four S T hsEq htEq htWindow hassoc
  · exact (K.one_three T S htEq hsEq hsFromTWindow hassoc.symm).symm
  · exact (K.two_three T S htEq hsEq hsFromTWindow hassoc.symm).symm
  · exact K.three_three S T hsEq htEq htWindow hassoc
  · exact K.three_four S T hsEq htEq htWindow hassoc
  · exact (K.one_four T S htEq hsEq hsFromTWindow hassoc.symm).symm
  · exact (K.two_four T S htEq hsEq hsFromTWindow hassoc.symm).symm
  · exact (K.three_four T S htEq hsEq hsFromTWindow hassoc.symm).symm
  · exact K.four_four S T hsEq htEq htWindow hassoc

/-- The ten formula kernels assemble exactly the pairwise side witness used
by the production capacity theorem. -/
noncomputable def roleCollisionWitnesses
    (locality : SourceLocalityCertificates P W F)
    (K : RealizedSameSideKernels (F := F) rows) :
    RoleCollisionWitnesses P W F
      (localCasesOfRealizedRows (F := F) rows) where
  locality := locality
  sideOf := realizedArrivalSide (F := F) rows
  same_side_unique_in_window := K.same_side_unique_in_window locality

end RealizedSameSideKernels

end Erdos957RoleCollisions

#print axioms Erdos957RoleCollisions.no_three_common_unit_target_in_window
#print axioms Erdos957RoleCollisions.SecondaryRoleCollisionKernels.noThreeRoleCollisionWitnesses
#print axioms Erdos957RoleCollisions.RoleAnchoredSameSideKernels.secondaryRoleCollisionKernels
#print axioms Erdos957RoleCollisions.RealizedSameSideKernels.roleCollisionWitnesses
