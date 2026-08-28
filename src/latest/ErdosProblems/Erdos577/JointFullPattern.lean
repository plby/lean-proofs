import ErdosProblems.Erdos577.JointFullCounts

/-! The exact remaining full-row configuration, with both diagonals and all four rows. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} {G : SimpleGraph V}

def FullPattern (v : Quadrilateral G) (x y z w : V) : Prop :=
  (∀ i : Fin 4, G.Adj x (v i) ↔ i = 0) ∧
  (∀ i : Fin 4, G.Adj y (v i) ↔ i = 1 ∨ i = 2) ∧
  (∀ i : Fin 4, G.Adj z (v i)) ∧
  (∀ i : Fin 4, G.Adj w (v i) ↔ i = 1 ∨ i = 2) ∧ PawBlock.OnlyFirst v

variable [DecidableEq V] [DecidableRel G.Adj]

theorem FinalRows.full_middle_pattern {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4)
    (hxrow : ∀ i : Fin 4, G.Adj x (v i) ↔ i = 0)
    (hw1 : G.Adj w (v 1)) (hw2 : G.Adj w (v 2)) : FullPattern v x y z w := by
  have hx0 := (hxrow 0).mpr rfl
  obtain ⟨_, hw, hy, _, _⟩ := h.full_first_counts hz hx0
  have hdiag := h.full_middle_low_absent hz hx0 hw1 hw2
  obtain ⟨hy1, hy2⟩ := h.full_middle_exposed hz hdiag hy hw1 hw2
  have hfull := h.full_distinguished_row hz
  obtain ⟨_, _, _, hyz, hyw, hzw⟩ := JointCore.four_distinct h.distinct
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have hyo : y ∉ ({w, v 1, v 2} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hyw, fun he ↦ h.y_out (he.symm ▸ hm 1), fun he ↦ h.y_out (he.symm ▸ hm 2)⟩
  obtain ⟨hquad, hfive⟩ := shared_pair_five w y (v 1) (v 2) hyo
    hw1 hw2 (v.adjacent 1) hy1 hy2
  have ht : G.IsNClique 3 {z, v 0, v 3} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hfull 0, hfull 3, (v.adjacent 3).symm⟩
  obtain ⟨hdis, hcover⟩ := triple_edge_split v z w y h.z_out h.w_out h.y_out hzw hyz.symm
  have hcover' : ({z, v 0, v 3} : Finset V) ∪ {w, y, v 1, v 2} =
      insert y ({z, w} ∪ v.support) := by
    rw [hcover]
    simp only [insert_union, singleton_union]
    rw [insert_comm w y, insert_comm z y]
  have hhigh := h.high_diagonal_of_gain hdiag y (Or.inr rfl) ht hquad hdis hcover' hfive
  exact ⟨hxrow, exact_two_row v y 1 2 (by decide) hy.le hy1 hy2, hfull,
    exact_two_row v w 1 2 (by decide) hw.le hw1 hw2, hhigh, hdiag⟩

theorem FinalRows.full_first_pattern {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4)
    (hxrow : ∀ i : Fin 4, G.Adj x (v i) ↔ i = 0) :
    degreeIn G x v.support + degreeIn G y v.support +
      degreeIn G z v.support + degreeIn G w v.support = 9 ∧
      ∃ q : Quadrilateral G, q.support = v.support ∧ FullPattern q x y z w := by
  obtain ⟨_, _, _, hsum, hchoice⟩ := h.full_first_counts hz ((hxrow 0).mpr rfl)
  refine ⟨hsum, ?_⟩
  rcases hchoice with ⟨hw1, hw2⟩ | ⟨hw2, hw3⟩
  · exact ⟨v, rfl, h.full_middle_pattern hz hxrow hw1 hw2⟩
  · have hxrev : ∀ i : Fin 4, G.Adj x (v.reverse i) ↔ i = 0 :=
      fun i ↦ (hxrow (-i)).trans neg_eq_zero
    exact ⟨v.reverse, v.reverse_support, (h.reverse_full hz).full_middle_pattern
      (by rwa [Quadrilateral.reverse_support]) hxrev hw3 hw2⟩

end Erdos577.JointFinal
