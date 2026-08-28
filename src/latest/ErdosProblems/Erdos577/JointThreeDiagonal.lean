import ErdosProblems.Erdos577.JointPairLabels

/-! The exact three-contact distinguished row and its absent low diagonal. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma PairRows.three_counts {v : Quadrilateral G} {x y z w : V} (h : PairRows v x y z w)
    (hz : degreeIn G z v.support = 3) (hw : degreeIn G w v.support ≤ 3) :
    2 ≤ degreeIn G w v.support ∧
      4 ≤ degreeIn G x v.support + degreeIn G w v.support ∧
      3 ≤ degreeIn G x v.support + degreeIn G y v.support := by
  have hx := h.x_bound
  have hy := h.y_bound
  have hn := h.nine
  omega

lemma included_three_exact (v : Quadrilateral G) (z : V)
    (hz : degreeIn G z v.support = 3)
    (hthree : ∀ i : Fin 4, i ≠ 3 → G.Adj z (v i)) :
    ∀ i : Fin 4, G.Adj z (v i) ↔ i ≠ 3 := by
  have hnot : ¬G.Adj z (v 3) := by
    intro h3
    have hfull : ∀ u ∈ v.support, G.Adj z u := by
      intro u hu
      obtain ⟨i, rfl⟩ := (v.mem_support u).mp hu
      by_cases hi : i = 3
      · subst i
        exact h3
      · exact hthree i hi
    have he := (degreeIn_eq_card_iff (G := G) z v.support).mpr hfull
    rw [hz, v.card_support] at he
    omega
  intro i
  exact ⟨fun hi he ↦ hnot (he ▸ hi), hthree i⟩

theorem PairRows.three_low_diagonal_absent {v : Quadrilateral G} {x y z w : V}
    (h : PairRows v x y z w) (hz : degreeIn G z v.support = 3) :
    ¬G.Adj (v 1) (v 3) := by
  intro hdiag
  have hrep := three_row_universal v z h.z_out h.three hdiag
  have hdis := no_common_of_universal_insertion x w z v.support h.no_xw_z hrep
  have hpair := degree_pair_le_card x w v.support hdis
  have hcard := v.card_support
  have hy := h.y_bound
  have hn := h.nine
  have hsum : degreeIn G x v.support + degreeIn G w v.support = v.support.card := by omega
  have hcover := disjoint_rows_cover x w v.support hdis hsum
  have hyexact : degreeIn G y v.support = 2 := by omega
  obtain ⟨i, hi, hyrep⟩ := FullRow.replacement_in_first_three v y h.y_out hdiag (by omega)
  have hvi : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  rcases hcover (v i) hvi with hx | hw
  · exact h.no_xz_y ⟨v i, hvi, hx, h.three i hi, hyrep⟩
  · exact h.no_zw_y ⟨v i, hvi, h.three i hi, hw, hyrep⟩

end Erdos577.JointFinal
