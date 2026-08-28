import ErdosProblems.Erdos577.PairReplacements
import ErdosProblems.Erdos577.PathPatternARows
import ErdosProblems.Erdos577.CycleLabels

/-! A nonuniversal row of size at least three has an exact cyclic three-contact labeling. -/

namespace Erdos577.Quadrilateral

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma three_contacts_universal_of_diagonal (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (hrow : ∀ j : Fin 4, j ≠ 3 → G.Adj z (q j)) (hd : G.Adj (q 1) (q 3))
    (u : V) (hu : u ∈ q.support) : QuadOn G (insert z (q.support.erase u)) := by
  obtain ⟨i, rfl⟩ := (q.mem_support u).mp hu
  fin_cases i
  · exact q.replace_using_path z hz 0 1 3 2 (by decide) (by decide)
      (hrow 1 (by decide)) hd (q.adjacent 2).symm (hrow 2 (by decide))
  · exact q.replace_using_path z hz 1 0 3 2 (by decide) (by decide)
      (hrow 0 (by decide)) (q.adjacent 3).symm (q.adjacent 2).symm (hrow 2 (by decide))
  · exact q.replace_using_path z hz 2 0 3 1 (by decide) (by decide)
      (hrow 0 (by decide)) (q.adjacent 3).symm hd.symm (hrow 1 (by decide))
  · exact q.replace_using_path z hz 3 0 1 2 (by decide) (by decide)
      (hrow 0 (by decide)) (q.adjacent 0) (q.adjacent 1) (hrow 2 (by decide))

variable [DecidableRel G.Adj]

lemma exists_three_contact_labels (q : Quadrilateral G) (z : V)
    (h3 : degreeIn G z q.support = 3) :
    ∃ v : Quadrilateral G, v.support = q.support ∧
      ∀ j : Fin 4, G.Adj z (v j) ↔ j ≠ 3 := by
  have hex : ∃ j : Fin 4, ¬G.Adj z (q j) := by
    by_contra! hn
    have he : degreeIn G z q.support = q.support.card :=
      (degreeIn_eq_card_iff z q.support).mpr (by
        intro u hu
        obtain ⟨j, rfl⟩ := (q.mem_support u).mp hu
        exact hn j)
    rw [q.card_support] at he
    omega
  obtain ⟨j, hj⟩ := hex
  let v := q.rotate (j - 3)
  have hv : v.support = q.support := q.rotate_support (j - 3)
  have hn : ¬G.Adj z (v 3) := by
    change ¬G.Adj z (q (3 + (j - 3)))
    have he : (3 : Fin 4) + (j - 3) = j := by abel
    rw [he]
    exact hj
  exact ⟨v, hv, v.adj_iff_ne_three z (by rw [hv]; exact h3) hn⟩

lemma exists_nonuniversal_three_labels (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (h3 : 3 ≤ degreeIn G z q.support)
    (hnot : ¬∀ u ∈ q.support, QuadOn G (insert z (q.support.erase u))) :
    degreeIn G z q.support = 3 ∧ ∃ v : Quadrilateral G, v.support = q.support ∧
      (∀ j : Fin 4, G.Adj z (v j) ↔ j ≠ 3) ∧ ¬G.Adj (v 1) (v 3) := by
  have hb := degreeIn_le_card G z q.support
  rw [q.card_support] at hb
  have hn4 : degreeIn G z q.support ≠ 4 := by
    intro h4
    exact hnot (fun u hu ↦ (show QuadOn G q.support from ⟨q, rfl⟩).replace_of_degree_four hz h4 hu)
  have he3 : degreeIn G z q.support = 3 := by omega
  obtain ⟨v, hv, hrow⟩ := q.exists_three_contact_labels z he3
  refine ⟨he3, v, hv, hrow, ?_⟩
  intro hd
  apply hnot
  intro u hu
  rw [← hv] at hu ⊢
  exact v.three_contacts_universal_of_diagonal z (by rw [hv]; exact hz)
    (fun j hj ↦ (hrow j).mpr hj) hd u hu

end Erdos577.Quadrilateral
