import ErdosProblems.Erdos577.CliqueReplacementObstructions
import ErdosProblems.Erdos577.PathSaturatedRows
import ErdosProblems.Erdos577.PathPatternARows

/-! The eight insertion restrictions force the dense block in weighted pattern (13). -/

namespace Erdos577.PathBlock

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

structure ThirteenInsertionsExcluded (p : FourPath G) (s : Finset V) (b w : V) : Prop where
  row0 : ¬CommonReplacement G (p.vertices 1) (p.vertices 2) (p.vertices 0) s
  row1 : ¬CommonReplacement G (p.vertices 0) (p.vertices 3) (p.vertices 1) s
  row2 : ¬CommonReplacement G (p.vertices 3) w (p.vertices 2) s
  row3 : ¬CommonReplacement G (p.vertices 0) (p.vertices 2) w s
  row4 : ¬CommonReplacement G (p.vertices 0) b (p.vertices 2) s
  row5 : ¬CommonReplacement G (p.vertices 3) (p.vertices 2) w s
  row6 : ¬CommonReplacement G w b (p.vertices 3) s
  row7 : ¬CommonReplacement G w (p.vertices 2) (p.vertices 3) s

lemma ThirteenInsertionsExcluded.not_forward_A (p : FourPath G) (q : Quadrilateral G)
    (b w : V) (hn : ThirteenInsertionsExcluded p q.support b w) : ¬CommonA p q := by
  intro h
  exact hn.row0 (h 0 1 2 (by decide) (by decide) (by decide))

variable [DecidableRel G.Adj]

lemma PatternB.thirteen_paired_bound (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hcl : G.IsNClique 4 q.support)
    (h : PatternB p q) (hh : 9 ≤ contacts G p.support q.support)
    (b w : V) (hw : w ∉ q.support) (hn : ThirteenInsertionsExcluded p q.support b w) :
    contacts G p.support q.support + degreeIn G (p.vertices 0) q.support +
      degreeIn G (p.vertices 1) q.support + degreeIn G b q.support +
        degreeIn G w q.support ≤ 16 := by
  have hout (i : Fin 4) : p.vertices i ∉ q.support := by
    intro hv
    exact disjoint_left.mp hd ((p.mem_support _).mpr ⟨i, rfl⟩) hv
  obtain ⟨_, h1, _, _⟩ := h.row_bounds p q
  have hr2 : degreeIn G (p.vertices 1) q.support ≤ 2 := by
    by_contra! hbig
    have he : degreeIn G (p.vertices 1) q.support = 3 := by omega
    exact hn.row1 (h.common_for_middle p q hd hcl hh 1 (Or.inl rfl) he
      0 3 (by decide) (by decide) (by decide))
  obtain ⟨he, h0, hr, hc, hz⟩ := h.exact_nine p q hh hr2
  have hu : q 0 ∈ q.support := (q.mem_support _).mpr ⟨0, rfl⟩
  have hx := h.full_endpoint_adj p q 0 (Or.inl rfl) h0 0 (Or.inl rfl)
  have hy := h.full_endpoint_adj p q 3 (Or.inr rfl) hz 0 (Or.inl rfl)
  have hcu := h.full_middle_adj p q 2 hc 0 (by decide)
  have hnwu : ¬G.Adj w (q 0) := by
    intro hwu
    exact hn.row2 ⟨q 0, hu, hy, hwu,
      clique_replace_of_degree_three hcl (hout 2) (by omega) hu⟩
  have hw1 := no_common_replacement_degree_le_one hcl (p.vertices 0) (p.vertices 2)
    w hw hn.row3 (q 0) hu hx hcu hnwu
  have hb := no_common_replacement_degree_sum hcl (p.vertices 0) b (p.vertices 2)
    (hout 2) (by omega) hn.row4
  omega

lemma PatternA.thirteen_dense (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hcl : G.IsNClique 4 q.support)
    (h : PatternA p.reverse q) (hh : 9 ≤ contacts G p.support q.support)
    (b w : V) (hw : w ∉ q.support) (hn : ThirteenInsertionsExcluded p q.support b w)
    (hpair : 17 ≤ contacts G p.support q.support + degreeIn G (p.vertices 0) q.support +
      degreeIn G (p.vertices 1) q.support + degreeIn G b q.support + degreeIn G w q.support) :
    degreeIn G (p.vertices 0) q.support = 0 ∧ degreeIn G w q.support = 0 ∧
      degreeIn G b q.support = 4 ∧ degreeIn G (p.vertices 2) q.support = 4 ∧
      (∀ j : Fin 4, G.Adj (p.vertices 1) (q j) ↔ j ≠ 3) ∧
      (∀ j : Fin 4, G.Adj (p.vertices 3) (q j) ↔ j ≠ 3) := by
  have hout (i : Fin 4) : p.vertices i ∉ q.support := by
    intro hv
    exact disjoint_left.mp hd ((p.mem_support _).mpr ⟨i, rfl⟩) hv
  obtain ⟨hz3, hc3, hc4, hr3, hx0⟩ := h.row_bounds p.reverse q
  change degreeIn G (p.vertices 3) q.support ≤ 3 at hz3
  change 3 ≤ degreeIn G (p.vertices 2) q.support at hc3
  change degreeIn G (p.vertices 2) q.support ≤ 4 at hc4
  change degreeIn G (p.vertices 1) q.support ≤ 3 at hr3
  change degreeIn G (p.vertices 0) q.support = 0 at hx0
  obtain ⟨hz2, hr2⟩ := h.outer_two_le p.reverse q (by rw [p.reverse_support]; exact hh)
  change 2 ≤ degreeIn G (p.vertices 3) q.support at hz2
  change 2 ≤ degreeIn G (p.vertices 1) q.support at hr2
  have hbound (x y : V) :
      ((q.support.filter (G.Adj x)) ∪ (q.support.filter (G.Adj y))).card ≤ 4 := by
    rw [← q.card_support]
    exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  have hmiss (u : V) (hu : u ∈ q.support) (hzu : G.Adj (p.vertices 3) u) : ¬G.Adj w u := by
    intro hwu
    exact hn.row2 ⟨u, hu, hzu, hwu,
      clique_replace_of_degree_three hcl (hout 2) hc3 hu⟩
  obtain ⟨u, hu, hzu, hcu⟩ := common_neighbor_of_union_bound
    (p.vertices 3) (p.vertices 2) q.support 4 (hbound _ _) (by omega)
  have hw1 := no_common_replacement_degree_le_one hcl (p.vertices 3) (p.vertices 2)
    w hw hn.row5 u hu hzu hcu (hmiss u hu hzu)
  have hbw : degreeIn G b q.support + degreeIn G w q.support ≤ 4 := by
    by_contra! hlarge
    obtain ⟨z, hz, hbz, hwz⟩ := common_neighbor_of_union_bound b w q.support 4
      (hbound _ _) hlarge
    have hnz : ¬G.Adj (p.vertices 3) z := fun hh ↦ hmiss z hz hh hwz
    have herase := degreeIn_erase_add G (p.vertices 3) z hz
    rw [if_neg hnz] at herase
    exact hn.row6 ⟨z, hz, hwz, hbz,
      (clique_replace_iff_two_contacts hcl (hout 3) hz).mpr (by omega)⟩
  have hsum := p.contacts_support q.support
  have hr : degreeIn G (p.vertices 1) q.support = 3 := by omega
  have hc : degreeIn G (p.vertices 2) q.support = 4 := by omega
  have hz : degreeIn G (p.vertices 3) q.support = 3 := by omega
  have hw0 : degreeIn G w q.support = 0 := by
    apply (degreeIn_eq_zero_iff (G := G) _ _).mpr
    intro z hzmem hwz
    exact hn.row7 ⟨z, hzmem, hwz, q.adj_of_degree_four (p.vertices 2) hc z hzmem,
      clique_replace_of_degree_three hcl (hout 3) (by omega) hzmem⟩
  refine ⟨hx0, hw0, by omega, hc, ?_, ?_⟩
  · exact q.adj_iff_ne_three (p.vertices 1) hr
      (h.outer_nonadjacent p.reverse q 2 (Or.inr rfl))
  · exact q.adj_iff_ne_three (p.vertices 3) hz
      (h.outer_nonadjacent p.reverse q 0 (Or.inl rfl))

end Erdos577.PathBlock
