import ErdosProblems.Erdos577.JointFullOldDegree

/-! A unique first-column old contact forces both remaining degrees and their adjacent row. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem FinalRows.full_first_counts {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4) (hx0 : G.Adj x (v 0)) :
    ¬G.Adj w (v 0) ∧ degreeIn G w v.support = 2 ∧ degreeIn G y v.support = 2 ∧
      degreeIn G x v.support + degreeIn G y v.support +
        degreeIn G z v.support + degreeIn G w v.support = 9 ∧
      ((G.Adj w (v 1) ∧ G.Adj w (v 2)) ∨ (G.Adj w (v 2) ∧ G.Adj w (v 3))) := by
  have hdis := h.full_distinguished_disjoint hz
  have hw0 : ¬G.Adj w (v 0) := fun hh ↦
    hdis (v 0) ((v.mem_support _).mpr ⟨0, rfl⟩) ⟨hx0, hh⟩
  have hhigh : ¬(G.Adj w (v 0) ∧ G.Adj w (v 2)) := fun hh ↦ hw0 hh.1
  have hH := (degree_pair_le_one_iff w (v 0) (v 2) (v.injective.ne (by decide))).mpr hhigh
  have hL := (degree_pair_le_one_iff w (v 1) (v 3) (v.injective.ne (by decide))).mpr
    h.toPairRows.no_low_w
  have hsplit := opposite_degree_split v w
  have hx := h.full_old_degree hz
  have hy := h.y_bound
  have hn := h.nine
  have hw : degreeIn G w v.support = 2 := by omega
  refine ⟨hw0, hw, by omega, by omega, ?_⟩
  rcases adjacent_neighbors_of_degree_two v w hw hhigh h.toPairRows.no_low_w with
    hh | hh | hh | hh
  · exact False.elim (hw0 hh.1)
  · exact Or.inl hh
  · exact Or.inr hh
  · exact False.elim (hw0 hh.1)

theorem FinalRows.full_middle_low_absent {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4)
    (hx0 : G.Adj x (v 0)) (hw1 : G.Adj w (v 1)) (hw2 : G.Adj w (v 2)) :
    ¬G.Adj (v 1) (v 3) := by
  intro hh
  have hrep := v.replace_using_path w h.w_out 0 1 3 2 (by decide) (by decide)
    hw1 hh (v.adjacent 2).symm hw2
  exact h.no_xz_w ⟨v 0, (v.mem_support _).mpr ⟨0, rfl⟩, hx0,
    h.full_distinguished_row hz 0, hrep⟩

theorem FinalRows.full_middle_exposed {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4)
    (hdiag : ¬G.Adj (v 1) (v 3)) (hy : degreeIn G y v.support = 2)
    (hw1 : G.Adj w (v 1)) (hw2 : G.Adj w (v 2)) :
    G.Adj y (v 1) ∧ G.Adj y (v 2) := by
  rcases adjacent_neighbors_of_degree_two v y hy h.no_high_y h.toPairRows.no_low_y with
    ⟨hy0, hy1⟩ | hh | ⟨hy2, hy3⟩ | ⟨hy0, hy3⟩
  · exact False.elim ((h.reverse_full hz).extreme_contact_false (fun hh ↦ hdiag hh.symm)
      y (Or.inr rfl) hy0 hy1 (Or.inr hw2))
  · exact hh
  · exact False.elim (h.reflect_highs.extreme_contact_false hdiag
      y (Or.inr rfl) hy2 hy3 (Or.inl hw1))
  · exact False.elim (h.extreme_contact_false hdiag y (Or.inr rfl) hy0 hy3 (Or.inl hw1))

end Erdos577.JointFinal
