import ErdosProblems.Erdos577.JointThreeConclusion

/-! Universal insertion and cyclic transport for a full distinguished row. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma FinalRows.full_distinguished_row {v : Quadrilateral G} {x y z w : V}
    (_h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4) :
    ∀ i : Fin 4, G.Adj z (v i) := by
  have hfull := (degreeIn_eq_card_iff (G := G) z v.support).mp (hz.trans v.card_support.symm)
  exact fun i ↦ hfull (v i) ((v.mem_support _).mpr ⟨i, rfl⟩)

lemma FinalRows.full_distinguished_replace {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4) :
    ∀ u ∈ v.support, QuadOn G (insert z (v.support.erase u)) := by
  intro u hu
  exact (show QuadOn G v.support from ⟨v, rfl⟩).replace_of_degree_four h.z_out hz hu

lemma FinalRows.full_distinguished_disjoint {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4) :
    ∀ u ∈ v.support, ¬(G.Adj x u ∧ G.Adj w u) :=
  no_common_of_universal_insertion x w z v.support h.no_xw_z (h.full_distinguished_replace hz)

lemma FinalRows.rotate_full {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4) (i : Fin 4) :
    FinalRows (v.rotate i) x y z w := by
  have hfull := h.full_distinguished_row hz
  refine h.with_labels _ (v.rotate_support i) (fun j _ ↦ hfull (j + i)) ?_ ?_
  · fin_cases i
    · exact h.no_high_x
    · exact h.toPairRows.no_low_x
    · exact fun hh ↦ h.no_high_x hh.symm
    · exact fun hh ↦ h.toPairRows.no_low_x hh.symm
  · fin_cases i
    · exact h.no_high_y
    · exact h.toPairRows.no_low_y
    · exact fun hh ↦ h.no_high_y hh.symm
    · exact fun hh ↦ h.toPairRows.no_low_y hh.symm

lemma FinalRows.reverse_full {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 4) :
    FinalRows v.reverse x y z w := by
  have hfull := h.full_distinguished_row hz
  exact h.with_labels _ v.reverse_support (fun i _ ↦ hfull (-i)) h.no_high_x h.no_high_y

end Erdos577.JointFinal
