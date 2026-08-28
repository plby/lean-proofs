import ErdosProblems.Erdos577.JointPairLowBounds

/-! A leaf on both highs forces a common distinguished high and then excludes the low diagonal. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma PairRows.low_distinguished_disjoint {v : Quadrilateral G} {x y z w : V}
    (h : PairRows v x y z w) (u : V) (hu : u = x ∨ u = y)
    (hu0 : G.Adj u (v 0)) (hu2 : G.Adj u (v 2))
    (i : Fin 4) (hi : i = 1 ∨ i = 3) : ¬(G.Adj z (v i) ∧ G.Adj w (v i)) := by
  rintro ⟨hz, hw⟩
  have hout : u ∉ v.support := by
    rcases hu with rfl | rfl
    · exact h.x_out
    · exact h.y_out
  have hrep := opposite_replace v u hout hu0 hu2 i hi
  have hh : CommonReplacement G z w u v.support :=
    ⟨v i, (v.mem_support _).mpr ⟨i, rfl⟩, hz, hw, hrep⟩
  rcases hu with rfl | rfl
  · exact h.no_zw_x hh
  · exact h.no_zw_y hh

lemma PairRows.common_high_of_leaf_high {v : Quadrilateral G} {x y z w : V}
    (h : PairRows v x y z w) (u : V) (hu : u = x ∨ u = y)
    (hu0 : G.Adj u (v 0)) (hu2 : G.Adj u (v 2)) :
    G.Adj w (v 0) ∨ G.Adj w (v 2) := by
  by_contra! hn
  have hwH : degreeIn G w {v 0, v 2} = 0 := by
    rw [degree_pair_eq w (v 0) (v 2) (v.injective.ne (by decide)), if_neg hn.1, if_neg hn.2]
  have hlow := degree_pair_le_card z w {v 1, v 3} (by
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact h.low_distinguished_disjoint u hu hu0 hu2 1 (Or.inl rfl)
    · exact h.low_distinguished_disjoint u hu hu0 hu2 3 (Or.inr rfl))
  have hcL : ({v 1, v 3} : Finset V).card = 2 :=
    card_pair_eq_two_iff.mpr (v.injective.ne (by decide : (1 : Fin 4) ≠ 3))
  have hcH : ({v 0, v 2} : Finset V).card = 2 :=
    card_pair_eq_two_iff.mpr (v.injective.ne (by decide : (0 : Fin 4) ≠ 2))
  rw [hcL] at hlow
  have hzH := degreeIn_le_card G z {v 0, v 2}
  rw [hcH] at hzH
  have hz := opposite_degree_split v z
  have hw := opposite_degree_split v w
  have hfive := h.distinguished_five
  omega

lemma PairRows.no_high_x_of_diagonal {v : Quadrilateral G} {x y z w : V}
    (h : PairRows v x y z w) (hdiag : G.Adj (v 1) (v 3)) :
    ¬(G.Adj x (v 0) ∧ G.Adj x (v 2)) := by
  rintro ⟨hx0, hx2⟩
  have hrep := three_row_universal v z h.z_out h.three hdiag
  have hdis := no_common_of_universal_insertion x w z v.support h.no_xw_z hrep
  rcases h.common_high_of_leaf_high x (Or.inl rfl) hx0 hx2 with hw0 | hw2
  · exact hdis (v 0) ((v.mem_support _).mpr ⟨0, rfl⟩) ⟨hx0, hw0⟩
  · exact hdis (v 2) ((v.mem_support _).mpr ⟨2, rfl⟩) ⟨hx2, hw2⟩

lemma PairRows.no_high_y_of_diagonal {v : Quadrilateral G} {x y z w : V}
    (h : PairRows v x y z w) (hdiag : G.Adj (v 1) (v 3)) :
    ¬(G.Adj y (v 0) ∧ G.Adj y (v 2)) := by
  rintro ⟨hy0, hy2⟩
  have hrep := three_row_universal v z h.z_out h.three hdiag
  have hdis := no_common_of_universal_insertion x w z v.support h.no_xw_z hrep
  have hpair (a b : V) (hn : ¬CommonReplacement G a b y v.support) :
      ∀ u ∈ ({v 1, v 3} : Finset V), ¬(G.Adj a u ∧ G.Adj b u) := by
    intro u hu hab
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hn ⟨v 1, (v.mem_support _).mpr ⟨1, rfl⟩, hab.1, hab.2,
        opposite_replace v y h.y_out hy0 hy2 1 (Or.inl rfl)⟩
    · exact hn ⟨v 3, (v.mem_support _).mpr ⟨3, rfl⟩, hab.1, hab.2,
        opposite_replace v y h.y_out hy0 hy2 3 (Or.inr rfl)⟩
  have hlow := degree_triple_le_card x z w {v 1, v 3}
    (hpair x z h.no_xz_y) (hpair x w h.no_xw_y) (hpair z w h.no_zw_y)
  have hcL : ({v 1, v 3} : Finset V).card = 2 :=
    card_pair_eq_two_iff.mpr (v.injective.ne (by decide : (1 : Fin 4) ≠ 3))
  have hcH : ({v 0, v 2} : Finset V).card = 2 :=
    card_pair_eq_two_iff.mpr (v.injective.ne (by decide : (0 : Fin 4) ≠ 2))
  have hHsub : ({v 0, v 2} : Finset V) ⊆ v.support :=
    insert_subset ((v.mem_support _).mpr ⟨0, rfl⟩)
      (singleton_subset_iff.mpr ((v.mem_support _).mpr ⟨2, rfl⟩))
  have hhigh := degree_pair_le_card x w {v 0, v 2} (fun u hu ↦ hdis u (hHsub hu))
  have hzH := degreeIn_le_card G z {v 0, v 2}
  rw [hcL] at hlow
  rw [hcH] at hhigh hzH
  have hx := opposite_degree_split v x
  have hz := opposite_degree_split v z
  have hw := opposite_degree_split v w
  have hseven := h.three_rows_seven
  omega

theorem PairRows.high_diagonal_false {v : Quadrilateral G} {x y z w : V}
    (h : PairRows v x y z w) (u : V) (hu : u = x ∨ u = y)
    (hu0 : G.Adj u (v 0)) (hu2 : G.Adj u (v 2)) (hdiag : G.Adj (v 1) (v 3)) : False := by
  rcases hu with rfl | rfl
  · exact h.no_high_x_of_diagonal hdiag ⟨hu0, hu2⟩
  · exact h.no_high_y_of_diagonal hdiag ⟨hu0, hu2⟩

end Erdos577.JointFinal
