import ErdosProblems.Erdos577.Counting

/-! Row-count consequences of ten and eleven contacts between a triple and a four-set. -/

namespace Erdos577

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma exists_row_gt_of_contacts {t q : Finset V} {n : ℕ}
    (h : n * t.card < contacts G t q) : ∃ v ∈ t, n < degreeIn G v q := by
  by_contra hn
  have hall : ∀ v ∈ t, degreeIn G v q ≤ n := by
    intro v hv
    by_contra hnot
    exact hn ⟨v, hv, by omega⟩
  have hsum : contacts G t q ≤ ∑ _v ∈ t, n := sum_le_sum hall
  simp only [sum_const, smul_eq_mul] at hsum
  rw [Nat.mul_comm] at hsum
  omega

lemma contacts_erase_add {t q : Finset V} {v : V} (hv : v ∈ t) :
    contacts G (t.erase v) q + degreeIn G v q = contacts G t q := sum_erase_add _ _ hv

omit [DecidableEq V] in
lemma two_high_rows_of_ten {t q : Finset V} (ht : t.card = 3) (hq : q.card = 4)
    (h : 10 ≤ contacts G t q) :
    ∃ u ∈ t, ∃ v ∈ t, u ≠ v ∧ 3 ≤ degreeIn G u q ∧ 3 ≤ degreeIn G v q := by
  classical
  obtain ⟨u, hu, hdu⟩ := exists_row_gt_of_contacts (G := G) (n := 2) (q := q)
    (by omega : 2 * t.card < contacts G t q)
  have he := contacts_erase_add (G := G) (q := q) hu
  have hu4 := degreeIn_le_card G u q
  rw [hq] at hu4
  have hcard : (t.erase u).card = 2 := by rw [card_erase_of_mem hu, ht]
  obtain ⟨v, hv, hdv⟩ := exists_row_gt_of_contacts (G := G) (n := 2) (q := q)
    (by omega : 2 * (t.erase u).card < contacts G (t.erase u) q)
  exact ⟨u, hu, v, (mem_erase.mp hv).2, Ne.symm (mem_erase.mp hv).1, by omega, by omega⟩

omit [DecidableEq V] in
lemma every_row_high_of_eleven {t q : Finset V} (ht : t.card = 3) (hq : q.card = 4)
    (h : 11 ≤ contacts G t q) {v : V} (hv : v ∈ t) : 3 ≤ degreeIn G v q := by
  classical
  have he := contacts_erase_add (G := G) (q := q) hv
  have hupper := contacts_le_card_mul G (t.erase v) q
  rw [card_erase_of_mem hv, ht, hq] at hupper
  omega

end Erdos577
