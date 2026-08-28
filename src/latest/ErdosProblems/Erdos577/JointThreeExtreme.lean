import ErdosProblems.Erdos577.JointThreeGainGeometry

/-! A three-contact distinguished row excludes both terminal contacts at the extreme pair. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma middle_absent_row (v : Quadrilateral G) (w : V) (hpos : 2 ≤ degreeIn G w v.support)
    (h1 : ¬G.Adj w (v 1)) (h2 : ¬G.Adj w (v 2)) :
    G.Adj w (v 0) ∧ G.Adj w (v 3) ∧ degreeIn G w v.support = 2 := by
  have he := opposite_degree_split v w
  rw [degree_pair_eq w (v 0) (v 2) (v.injective.ne (by decide)),
    degree_pair_eq w (v 1) (v 3) (v.injective.ne (by decide)), if_neg h2, if_neg h1] at he
  by_cases h0 : G.Adj w (v 0)
  · by_cases h3 : G.Adj w (v 3)
    · rw [if_pos h0, if_pos h3] at he
      exact ⟨h0, h3, by omega⟩
    · rw [if_pos h0, if_neg h3] at he
      omega
  · by_cases h3 : G.Adj w (v 3)
    · rw [if_neg h0, if_pos h3] at he
      omega
    · rw [if_neg h0, if_neg h3] at he
      omega

theorem FinalRows.three_extreme_false {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 3)
    (u : V) (hu : u = x ∨ u = y) (hu0 : G.Adj u (v 0)) (hu3 : G.Adj u (v 3)) : False := by
  have hdiag := h.toPairRows.three_low_diagonal_absent hz
  have hwabs : ¬G.Adj w (v 1) ∧ ¬G.Adj w (v 2) :=
    not_or.mp (fun hh ↦ h.extreme_contact_false hdiag u hu hu0 hu3 hh)
  have hwpos : 2 ≤ degreeIn G w v.support := by
    have hh := h.toPairRows.distinguished_five
    omega
  obtain ⟨hw0, hw3, hwexact⟩ := middle_absent_row v w hwpos hwabs.1 hwabs.2
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have hx3 : ¬G.Adj x (v 3) := fun hh ↦ h.no_xw_z ⟨v 3, hm 3, hh, hw3,
    opposite_replace v z h.z_out (h.three 0 (by decide)) (h.three 2 (by decide)) 3 (Or.inr rfl)⟩
  rcases hu with hu | hu
  · exact hx3 (hu ▸ hu3)
  · subst u
    obtain ⟨_, _, _, hyz, hyw, hzw⟩ := JointCore.four_distinct h.distinct
    have hyo : y ∉ ({w, v 0, v 3} : Finset V) := by
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hyw, fun he ↦ h.y_out (he.symm ▸ hm 0), fun he ↦ h.y_out (he.symm ▸ hm 3)⟩
    obtain ⟨hquad, hfive⟩ := shared_pair_five w y (v 0) (v 3) hyo
      hw0 hw3 (v.adjacent 3).symm hu0 hu3
    have ht : G.IsNClique 3 {z, v 1, v 2} := SimpleGraph.is3Clique_triple_iff.mpr
      ⟨h.three 1 (by decide), h.three 2 (by decide), v.adjacent 1⟩
    obtain ⟨hdis, hcover⟩ := triple_middle_split v z w y h.z_out h.w_out h.y_out hzw hyz.symm
    have hcover' : ({z, v 1, v 2} : Finset V) ∪ {w, y, v 0, v 3} =
        insert y ({z, w} ∪ v.support) := by
      rw [hcover]
      simp only [insert_union, singleton_union]
      rw [insert_comm w y, insert_comm z y]
    have hhigh := h.high_diagonal_of_gain hdiag y (Or.inr rfl) ht hquad hdis hcover' hfive
    have hyrep := v.replace_using_path y h.y_out 1 0 2 3 (by decide) (by decide)
      hu0 hhigh (v.adjacent 2) hu3
    have hx1 : ¬G.Adj x (v 1) := fun hh ↦
      h.no_xz_y ⟨v 1, hm 1, hh, h.three 1 (by decide), hyrep⟩
    have hxL : degreeIn G x {v 1, v 3} = 0 := by
      rw [degree_pair_eq x (v 1) (v 3) (v.injective.ne (by decide)), if_neg hx1, if_neg hx3]
    have hxH := (degree_pair_le_one_iff x (v 0) (v 2) (v.injective.ne (by decide))).mpr h.no_high_x
    have hsplit := opposite_degree_split v x
    have hy := h.y_bound
    have hn := h.nine
    omega

end Erdos577.JointFinal
