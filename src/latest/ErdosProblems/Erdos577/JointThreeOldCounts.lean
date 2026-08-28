import ErdosProblems.Erdos577.JointThreeFactor

/-! The exact remaining rows when the old terminal meets the first adjacent pair. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem FinalRows.three_old_counts {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 3)
    (hxrow : ∀ i : Fin 4, G.Adj x (v i) ↔ (3 : ℕ).testBit i.val = true) :
    ¬G.Adj w (v 1) ∧ G.Adj w (v 3) ∧ (G.Adj w (v 0) ∨ G.Adj w (v 2)) ∧
      degreeIn G w v.support = 2 ∧ degreeIn G y v.support = 2 ∧
      (∀ i : Fin 4, G.Adj y (v i) ↔ (6 : ℕ).testBit i.val = true) := by
  have hx0 := (hxrow 0).mpr (by decide)
  have hx1 := (hxrow 1).mpr (by decide)
  have hx2 : degreeIn G x v.support = 2 := by
    rw [v.degree_eq_mask x 3 hxrow]
    decide +kernel
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have hw1 : ¬G.Adj w (v 1) := fun hh ↦ h.no_xw_z ⟨v 1, hm 1, hx1, hh,
    opposite_replace v z h.z_out (h.three 0 (by decide)) (h.three 2 (by decide)) 1 (Or.inl rfl)⟩
  have hwhigh : ¬(G.Adj w (v 0) ∧ G.Adj w (v 2)) := fun hh ↦
    h.no_xz_w ⟨v 1, hm 1, hx1, h.three 1 (by decide),
      opposite_replace v w h.w_out hh.1 hh.2 1 (Or.inl rfl)⟩
  have hwH := (degree_pair_le_one_iff w (v 0) (v 2) (v.injective.ne (by decide))).mpr hwhigh
  have hwpos : 2 ≤ degreeIn G w v.support := by
    have hh := h.toPairRows.distinguished_five
    omega
  have hsplit := opposite_degree_split v w
  have hw3 : G.Adj w (v 3) := by
    by_contra hn
    have hL : degreeIn G w {v 1, v 3} = 0 := by
      rw [degree_pair_eq w (v 1) (v 3) (v.injective.ne (by decide)), if_neg hw1, if_neg hn]
    omega
  have hwL : degreeIn G w {v 1, v 3} = 1 := by
    rw [degree_pair_eq w (v 1) (v 3) (v.injective.ne (by decide)), if_neg hw1, if_pos hw3]
  have hwexact : degreeIn G w v.support = 2 := by omega
  have hwchoice : G.Adj w (v 0) ∨ G.Adj w (v 2) := by
    by_contra! hn
    have hH : degreeIn G w {v 0, v 2} = 0 := by
      rw [degree_pair_eq w (v 0) (v 2) (v.injective.ne (by decide)), if_neg hn.1, if_neg hn.2]
    omega
  have hyexact : degreeIn G y v.support = 2 := by
    have hn := h.nine
    have hy := h.y_bound
    omega
  refine ⟨hw1, hw3, hwchoice, hwexact, hyexact, ?_⟩
  rcases h.three_leaf_rows hz y (Or.inr rfl) hyexact with hyrow | hyrow
  · exact False.elim (h.parallel_factor_false hx0 hx1
      ((hyrow 0).mpr (by decide)) ((hyrow 1).mpr (by decide)) hw3)
  · exact hyrow

end Erdos577.JointFinal
