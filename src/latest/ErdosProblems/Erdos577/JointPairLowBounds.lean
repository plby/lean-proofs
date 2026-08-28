import ErdosProblems.Erdos577.JointPairRows

/-! The three low-pair bounds follow from the original asymmetric insertion prohibitions. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma opposite_force_zero (v : Quadrilateral G) (u z w : V)
    (hu : u ∉ v.support) (hz : z ∉ v.support)
    (hu1 : G.Adj u (v 1)) (hu3 : G.Adj u (v 3))
    (hz0 : G.Adj z (v 0)) (hz2 : G.Adj z (v 2))
    (hno1 : ¬CommonReplacement G u w z v.support)
    (hno2 : ¬CommonReplacement G z w u v.support) : degreeIn G w v.support = 0 := by
  apply (degreeIn_eq_zero_iff (G := G) w v.support).mpr
  intro a ha hw
  obtain ⟨i, rfl⟩ := (v.mem_support a).mp ha
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  fin_cases i
  · exact hno2 ⟨v 0, hm 0, hz0, hw, low_pair_replace v u hu hu1 hu3 0 (Or.inl rfl)⟩
  · exact hno1 ⟨v 1, hm 1, hu1, hw, opposite_replace v z hz hz0 hz2 1 (Or.inl rfl)⟩
  · exact hno2 ⟨v 2, hm 2, hz2, hw, low_pair_replace v u hu hu1 hu3 2 (Or.inr rfl)⟩
  · exact hno1 ⟨v 3, hm 3, hu3, hw, opposite_replace v z hz hz0 hz2 3 (Or.inr rfl)⟩

lemma PairRows.low_columns {v : Quadrilateral G} {x y z w : V} (h : PairRows v x y z w)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) : ¬(G.Adj x (v i) ∧ G.Adj w (v i)) := by
  rintro ⟨hx, hw⟩
  exact h.no_xw_z ⟨v i, (v.mem_support _).mpr ⟨i, rfl⟩, hx, hw,
    opposite_replace v z h.z_out (h.three 0 (by decide)) (h.three 2 (by decide)) i hi⟩

lemma PairRows.no_low_x {v : Quadrilateral G} {x y z w : V} (h : PairRows v x y z w) :
    ¬(G.Adj x (v 1) ∧ G.Adj x (v 3)) := by
  rintro ⟨hx1, hx3⟩
  have hw := opposite_force_zero v x z w h.x_out h.z_out hx1 hx3
    (h.three 0 (by decide)) (h.three 2 (by decide)) h.no_xw_z h.no_zw_x
  have hz := degreeIn_le_card G z v.support
  rw [v.card_support] at hz
  have hx := h.x_bound
  have hy := h.y_bound
  have hn := h.nine
  omega

lemma PairRows.no_low_w {v : Quadrilateral G} {x y z w : V} (h : PairRows v x y z w) :
    ¬(G.Adj w (v 1) ∧ G.Adj w (v 3)) := by
  rintro ⟨hw1, hw3⟩
  have hx := opposite_force_zero v w z x h.w_out h.z_out hw1 hw3
    (h.three 0 (by decide)) (h.three 2 (by decide))
    (fun hh ↦ h.no_xw_z hh.symm) (fun hh ↦ h.no_xz_w hh.symm)
  have hp := h.x_pos
  omega

lemma PairRows.no_low_y {v : Quadrilateral G} {x y z w : V} (h : PairRows v x y z w) :
    ¬(G.Adj y (v 1) ∧ G.Adj y (v 3)) := by
  rintro ⟨hy1, hy3⟩
  have hnon (a : V) (hn : ¬CommonReplacement G a z y v.support)
      (i : Fin 4) (hi : i = 0 ∨ i = 2) : ¬G.Adj a (v i) := by
    intro ha
    have hi3 : i ≠ 3 := by rcases hi with rfl | rfl <;> decide
    exact hn ⟨v i, (v.mem_support _).mpr ⟨i, rfl⟩, ha, h.three i hi3,
      low_pair_replace v y h.y_out hy1 hy3 i hi⟩
  have hxH : degreeIn G x {v 0, v 2} = 0 := by
    rw [degree_pair_eq x (v 0) (v 2) (v.injective.ne (by decide)),
      if_neg (hnon x h.no_xz_y 0 (Or.inl rfl)), if_neg (hnon x h.no_xz_y 2 (Or.inr rfl))]
  have hwz : ¬CommonReplacement G w z y v.support := fun hh ↦ h.no_zw_y hh.symm
  have hwH : degreeIn G w {v 0, v 2} = 0 := by
    rw [degree_pair_eq w (v 0) (v 2) (v.injective.ne (by decide)),
      if_neg (hnon w hwz 0 (Or.inl rfl)), if_neg (hnon w hwz 2 (Or.inr rfl))]
  have hlow := degree_pair_le_card x w {v 1, v 3} (by
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact h.low_columns 1 (Or.inl rfl)
    · exact h.low_columns 3 (Or.inr rfl))
  have hcard : ({v 1, v 3} : Finset V).card = 2 :=
    card_pair_eq_two_iff.mpr (v.injective.ne (by decide : (1 : Fin 4) ≠ 3))
  rw [hcard] at hlow
  have hx := opposite_degree_split v x
  have hw := opposite_degree_split v w
  have hz := degreeIn_le_card G z v.support
  rw [v.card_support] at hz
  have hy := h.y_bound
  have hn := h.nine
  omega

theorem PairRows.low_pair_bounds {v : Quadrilateral G} {x y z w : V}
    (h : PairRows v x y z w) : degreeIn G x {v 1, v 3} ≤ 1 ∧
      degreeIn G y {v 1, v 3} ≤ 1 ∧ degreeIn G w {v 1, v 3} ≤ 1 := by
  have hne := v.injective.ne (by decide : (1 : Fin 4) ≠ 3)
  exact ⟨(degree_pair_le_one_iff x _ _ hne).mpr h.no_low_x,
    (degree_pair_le_one_iff y _ _ hne).mpr h.no_low_y,
    (degree_pair_le_one_iff w _ _ hne).mpr h.no_low_w⟩

end Erdos577.JointFinal
