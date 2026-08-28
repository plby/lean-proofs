import ErdosProblems.Erdos577.CycleLabels
import ErdosProblems.Erdos577.RowSaturationIncluded

/-! A two-contact row can be labeled as an adjacent pair or an opposite pair on the cycle. -/

namespace Erdos577.Quadrilateral

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma two_contact_pair_row (q : Quadrilateral G) (z : V) (opposite : Bool)
    (hdegree : degreeIn G z q.support = 2) (hzero : G.Adj z (q 0))
    (hother : G.Adj z (q (if opposite then 2 else 1))) :
    ∀ j : Fin 4, G.Adj z (q j) ↔ (if opposite then 5 else 3 : ℕ).testBit j.val = true := by
  apply q.row_saturated_of_included z (if opposite then 5 else 3)
  · intro j hj
    cases opposite <;> fin_cases j
    · exact hzero
    · exact hother
    · exact False.elim ((by decide : ¬(3 : ℕ).testBit 2 = true) hj)
    · exact False.elim ((by decide : ¬(3 : ℕ).testBit 3 = true) hj)
    · exact hzero
    · exact False.elim ((by decide : ¬(5 : ℕ).testBit 1 = true) hj)
    · exact hother
    · exact False.elim ((by decide : ¬(5 : ℕ).testBit 3 = true) hj)
  · rw [hdegree]
    cases opposite <;> decide +kernel

lemma exists_two_contact_labels (q : Quadrilateral G) (z : V)
    (hdegree : degreeIn G z q.support = 2) :
    ∃ v : Quadrilateral G, v.support = q.support ∧
      ((∀ j : Fin 4, G.Adj z (v j) ↔ (3 : ℕ).testBit j.val = true) ∨
        (∀ j : Fin 4, G.Adj z (v j) ↔ (5 : ℕ).testBit j.val = true)) := by
  obtain ⟨u, hu⟩ := card_pos.mp (by change 0 < degreeIn G z q.support; omega)
  obtain ⟨huq, hzu⟩ := mem_filter.mp hu
  obtain ⟨i, rfl⟩ := (q.mem_support u).mp huq
  let v := q.rotate i
  have hv : v.support = q.support := q.rotate_support i
  have hzero : G.Adj z (v 0) := by simpa only [v, rotate_apply, zero_add] using hzu
  have htwo : degreeIn G z v.support = 2 := by rw [hv, hdegree]
  have hex : ∃ j : Fin 4, j ≠ 0 ∧ G.Adj z (v j) := by
    by_contra! hnone
    have hbound := v.degree_le_mask z 1 (by
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        decide
      · exact False.elim (hnone j hj0 hj))
    change degreeIn G z v.support ≤ 1 at hbound
    omega
  obtain ⟨j, hj0, hj⟩ := hex
  fin_cases j
  · exact False.elim (hj0 rfl)
  · exact ⟨v, hv, Or.inl (v.two_contact_pair_row z false htwo hzero hj)⟩
  · exact ⟨v, hv, Or.inr (v.two_contact_pair_row z true htwo hzero hj)⟩
  · refine ⟨v.reverse, v.reverse_support.trans hv, Or.inl ?_⟩
    apply v.reverse.two_contact_pair_row z false (by rw [v.reverse_support]; exact htwo)
    · exact hzero
    · exact hj

end Erdos577.Quadrilateral
