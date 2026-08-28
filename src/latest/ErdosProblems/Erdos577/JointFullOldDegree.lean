import ErdosProblems.Erdos577.JointFullRows

/-! The full distinguished row excludes every two-contact old-terminal row. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma adjacent_neighbors_of_degree_two (v : Quadrilateral G) (u : V)
    (htwo : degreeIn G u v.support = 2)
    (hhigh : ¬(G.Adj u (v 0) ∧ G.Adj u (v 2)))
    (hlow : ¬(G.Adj u (v 1) ∧ G.Adj u (v 3))) :
    (G.Adj u (v 0) ∧ G.Adj u (v 1)) ∨ (G.Adj u (v 1) ∧ G.Adj u (v 2)) ∨
      (G.Adj u (v 2) ∧ G.Adj u (v 3)) ∨ (G.Adj u (v 0) ∧ G.Adj u (v 3)) := by
  have he := opposite_degree_split v u
  rw [degree_pair_eq u (v 0) (v 2) (v.injective.ne (by decide)),
    degree_pair_eq u (v 1) (v 3) (v.injective.ne (by decide)), htwo] at he
  by_cases h0 : G.Adj u (v 0) <;> by_cases h1 : G.Adj u (v 1) <;>
    by_cases h2 : G.Adj u (v 2) <;> by_cases h3 : G.Adj u (v 3) <;>
    simp [h0, h1, h2, h3] at hhigh hlow he ⊢

theorem FinalRows.full_extreme_at_second_false {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4)
    (hx0 : G.Adj x (v 0)) (hx3 : G.Adj x (v 3)) (hw2 : G.Adj w (v 2)) : False := by
  have hfull := h.full_distinguished_row hz
  have hdiag : ¬G.Adj (v 1) (v 3) := by
    intro hh
    have hrep := v.replace_using_path x h.x_out 2 0 1 3 (by decide) (by decide)
      hx0 (v.adjacent 0) hh hx3
    exact h.no_zw_x ⟨v 2, (v.mem_support _).mpr ⟨2, rfl⟩, hfull 2, hw2, hrep⟩
  exact h.extreme_contact_false hdiag x (Or.inl rfl) hx0 hx3 (Or.inr hw2)

theorem FinalRows.full_extreme_false {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4)
    (hx0 : G.Adj x (v 0)) (hx3 : G.Adj x (v 3)) : False := by
  have hdis := h.full_distinguished_disjoint hz
  have hw0 : ¬G.Adj w (v 0) := fun hh ↦
    hdis (v 0) ((v.mem_support _).mpr ⟨0, rfl⟩) ⟨hx0, hh⟩
  have hw3 : ¬G.Adj w (v 3) := fun hh ↦
    hdis (v 3) ((v.mem_support _).mpr ⟨3, rfl⟩) ⟨hx3, hh⟩
  have hwpos : 1 ≤ degreeIn G w v.support := by
    have hh := h.toPairRows.distinguished_five
    omega
  have hwchoice : G.Adj w (v 1) ∨ G.Adj w (v 2) := by
    by_contra! hn
    have he := opposite_degree_split v w
    rw [degree_pair_eq w (v 0) (v 2) (v.injective.ne (by decide)),
      degree_pair_eq w (v 1) (v 3) (v.injective.ne (by decide)),
      if_neg hw0, if_neg hn.2, if_neg hn.1, if_neg hw3] at he
    omega
  rcases hwchoice with hw1 | hw2
  · have hr := (h.rotate_full hz 3).reverse_full (by rwa [Quadrilateral.rotate_support])
    exact hr.full_extreme_at_second_false
      (by simpa only [Quadrilateral.reverse_support, Quadrilateral.rotate_support] using hz)
      hx3 hx0 hw1
  · exact h.full_extreme_at_second_false hz hx0 hx3 hw2

theorem FinalRows.full_old_degree {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4) :
    degreeIn G x v.support = 1 := by
  have hnot : degreeIn G x v.support ≠ 2 := by
    intro htwo
    rcases adjacent_neighbors_of_degree_two v x htwo h.no_high_x h.toPairRows.no_low_x with
      ⟨hx0, hx1⟩ | ⟨hx1, hx2⟩ | ⟨hx2, hx3⟩ | ⟨hx0, hx3⟩
    · exact (h.reverse_full hz).full_extreme_false
        (by rwa [Quadrilateral.reverse_support]) hx0 hx1
    · exact (h.rotate_full hz 2).full_extreme_false
        (by rwa [Quadrilateral.rotate_support]) hx2 hx1
    · exact h.reflect_highs.full_extreme_false
        (by simpa only [Quadrilateral.reverse_support, Quadrilateral.rotate_support] using hz)
        hx2 hx3
    · exact h.full_extreme_false hz hx0 hx3
  have hpos := h.x_pos
  have hbound := h.x_bound
  omega

end Erdos577.JointFinal
