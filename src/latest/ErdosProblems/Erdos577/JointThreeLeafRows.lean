import ErdosProblems.Erdos577.JointThreeRelabel

/-! Every two-contact terminal row is one of the two adjacent pairs in the distinguished triple. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem FinalRows.three_leaf_no_last {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 3)
    (u : V) (hu : u = x ∨ u = y) (htwo : degreeIn G u v.support = 2) :
    ¬G.Adj u (v 3) := by
  intro hu3
  have hu0 : ¬G.Adj u (v 0) := fun hh ↦ h.three_extreme_false hz u hu hh hu3
  have hu2 : ¬G.Adj u (v 2) := fun hh ↦ h.three_last_false hz u hu hh hu3
  have hnlow : ¬(G.Adj u (v 1) ∧ G.Adj u (v 3)) := by
    rcases hu with rfl | rfl
    · exact h.toPairRows.no_low_x
    · exact h.toPairRows.no_low_y
  have hu1 : ¬G.Adj u (v 1) := fun hh ↦ hnlow ⟨hh, hu3⟩
  have he := opposite_degree_split v u
  rw [degree_pair_eq u (v 0) (v 2) (v.injective.ne (by decide)),
    degree_pair_eq u (v 1) (v 3) (v.injective.ne (by decide)),
    if_neg hu0, if_neg hu2, if_neg hu1, if_pos hu3] at he
  omega

lemma middle_two_rows (v : Quadrilateral G) (u : V) (htwo : degreeIn G u v.support = 2)
    (h3 : ¬G.Adj u (v 3)) (hhigh : ¬(G.Adj u (v 0) ∧ G.Adj u (v 2))) :
    (∀ i : Fin 4, G.Adj u (v i) ↔ (3 : ℕ).testBit i.val = true) ∨
      (∀ i : Fin 4, G.Adj u (v i) ↔ (6 : ℕ).testBit i.val = true) := by
  have hH := (degree_pair_le_one_iff u (v 0) (v 2) (v.injective.ne (by decide))).mpr hhigh
  have hsplit := opposite_degree_split v u
  have h1 : G.Adj u (v 1) := by
    by_contra hn
    have hL : degreeIn G u {v 1, v 3} = 0 := by
      rw [degree_pair_eq u (v 1) (v 3) (v.injective.ne (by decide)), if_neg hn, if_neg h3]
    omega
  have hpair : G.Adj u (v 0) ∨ G.Adj u (v 2) := by
    by_contra! hn
    have hHzero : degreeIn G u {v 0, v 2} = 0 := by
      rw [degree_pair_eq u (v 0) (v 2) (v.injective.ne (by decide)), if_neg hn.1, if_neg hn.2]
    have hL : degreeIn G u {v 1, v 3} = 1 := by
      rw [degree_pair_eq u (v 1) (v 3) (v.injective.ne (by decide)), if_pos h1, if_neg h3]
    omega
  rcases hpair with h0 | h2
  · have hrow := exact_two_row v u 0 1 (by decide) htwo.le h0 h1
    have hf : ∀ i : Fin 4, i = 0 ∨ i = 1 ↔ (3 : ℕ).testBit i.val = true := by decide +kernel
    exact Or.inl (fun i ↦ (hrow i).trans (hf i))
  · have hrow := exact_two_row v u 1 2 (by decide) htwo.le h1 h2
    have hf : ∀ i : Fin 4, i = 1 ∨ i = 2 ↔ (6 : ℕ).testBit i.val = true := by decide +kernel
    exact Or.inr (fun i ↦ (hrow i).trans (hf i))

theorem FinalRows.three_leaf_rows {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 3)
    (u : V) (hu : u = x ∨ u = y) (htwo : degreeIn G u v.support = 2) :
    (∀ i : Fin 4, G.Adj u (v i) ↔ (3 : ℕ).testBit i.val = true) ∨
      (∀ i : Fin 4, G.Adj u (v i) ↔ (6 : ℕ).testBit i.val = true) := by
  apply middle_two_rows v u htwo (h.three_leaf_no_last hz u hu htwo)
  rcases hu with rfl | rfl
  · exact h.no_high_x
  · exact h.no_high_y

end Erdos577.JointFinal
