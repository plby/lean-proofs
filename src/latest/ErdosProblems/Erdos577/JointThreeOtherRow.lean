import ErdosProblems.Erdos577.JointThreeOldDegree

/-! The exposed-terminal gain and the proved low-pattern obstruction fix the other triple. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma three_row_of_missing (v : Quadrilateral G) (u : V) (i : Fin 4)
    (hdeg : degreeIn G u v.support = 3) (hmiss : ¬G.Adj u (v i)) :
    ∀ j : Fin 4, G.Adj u (v j) ↔ j ≠ i := by
  have hm (j : Fin 4) : v j ∈ v.support := (v.mem_support _).mpr ⟨j, rfl⟩
  have hsub : v.support.filter (G.Adj u) ⊆ v.support.erase (v i) := by
    intro a ha
    obtain ⟨ha, hua⟩ := mem_filter.mp ha
    exact mem_erase.mpr ⟨fun he ↦ hmiss (he ▸ hua), ha⟩
  have hcard : (v.support.erase (v i)).card = 3 := by
    rw [card_erase_of_mem (hm i), v.card_support]
  have he : v.support.filter (G.Adj u) = v.support.erase (v i) :=
    eq_of_subset_of_card_le hsub (by change _ ≤ degreeIn G u v.support; rw [hcard, hdeg])
  intro j
  constructor
  · intro hj hji
    exact hmiss (hji ▸ hj)
  · intro hji
    have hj : v j ∈ v.support.filter (G.Adj u) := by
      rw [he]
      exact mem_erase.mpr ⟨v.injective.ne hji, hm j⟩
    exact (mem_filter.mp hj).2

theorem FinalRows.three_other_no_last {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 3)
    (hw : degreeIn G w v.support = 3)
    (hyrow : ∀ i : Fin 4, G.Adj y (v i) ↔ (3 : ℕ).testBit i.val = true) :
    ¬G.Adj w (v 3) := by
  intro hw3
  have hw1 : ¬G.Adj w (v 1) := fun hh ↦ h.toPairRows.no_low_w ⟨hh, hw3⟩
  have hwrow := three_row_of_missing v w 1 hw hw1
  have hw0 := (hwrow 0).mpr (by decide)
  have hw2 := (hwrow 2).mpr (by decide)
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  obtain ⟨_, _, _, hyz, hyw, hzw⟩ := JointCore.four_distinct h.distinct
  have hzo : z ∉ ({w, v 2, v 3} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hzw, fun he ↦ h.z_out (he.symm ▸ hm 2), fun he ↦ h.z_out (he.symm ▸ hm 3)⟩
  obtain ⟨hquad, hfive⟩ := edge_triangle_five w z (v 2) (v 3) hzo
    hw2 hw3 (v.adjacent 2) h.pair_edge (Or.inl (h.three 2 (by decide)))
  rw [insert_comm w z] at hquad hfive
  have ht : G.IsNClique 3 {y, v 0, v 1} := SimpleGraph.is3Clique_triple_iff.mpr
    ⟨(hyrow 0).mpr (by decide), (hyrow 1).mpr (by decide), v.adjacent 0⟩
  obtain ⟨hdis, hcover⟩ := triple_first_split v y z w h.y_out h.z_out h.w_out hyz hyw
  have hdiag := h.toPairRows.three_low_diagonal_absent hz
  have hhigh := h.high_diagonal_of_gain hdiag y (Or.inr rfl) ht hquad hdis hcover hfive
  have hyv : ∀ i : Fin 4, G.Adj y (v.reverse i) ↔ (9 : ℕ).testBit i.val = true := by
    intro i
    fin_cases i
    · exact hyrow 0
    · exact hyrow 3
    · exact hyrow 2
    · exact hyrow 1
  have hwv : ∀ i : Fin 4, i ≠ 3 → G.Adj w (v.reverse i) := by
    intro i hi
    fin_cases i
    · exact hw0
    · exact hw3
    · exact hw2
    · exact False.elim (hi rfl)
  have hpos : 1 ≤ degreeIn G z {v.reverse 1, v.reverse 2} :=
    card_pos.mpr ⟨v 2, mem_filter.mpr ⟨by change v 2 ∈ ({v 3, v 2} : Finset V); simp,
      h.three 2 (by decide)⟩⟩
  exact h.low y (Or.inr rfl) v.reverse v.reverse_support
    ⟨hhigh, fun hh ↦ hdiag hh.symm⟩ hyv w z (Or.inr ⟨rfl, rfl⟩) hwv hpos

end Erdos577.JointFinal
