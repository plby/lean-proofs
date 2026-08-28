import ErdosProblems.Erdos577.FullLeafSparseTripleFactor

/-! Contact estimates and choices for the two sparse-uniqueness factors. -/

namespace Erdos577.FullLeafSparse

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma contacts_le_other_rows {t j : Finset V} {v : V} (hv : v ∈ t) :
    contacts G t j ≤ (t.card - 1) * j.card + degreeIn G v j := by
  classical
  have he := contacts_erase_add (G := G) (q := j) hv
  have hb := contacts_le_card_mul G (t.erase v) j
  rw [card_erase_of_mem hv] at hb
  omega

omit [DecidableEq V] in
lemma common_neighbor_of_degree_sum (t : Finset V) (v w : V)
    (hsum : t.card < degreeIn G v t + degreeIn G w t) :
    ∃ x ∈ t, G.Adj x v ∧ G.Adj x w := by
  classical
  have he := card_union_add_card_inter (t.filter (G.Adj v)) (t.filter (G.Adj w))
  have hb : ((t.filter (G.Adj v)) ∪ (t.filter (G.Adj w))).card ≤ t.card :=
    card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  change _ + _ = degreeIn G v t + degreeIn G w t at he
  obtain ⟨x, hx⟩ := card_pos.mp
    (show 0 < ((t.filter (G.Adj v)) ∩ (t.filter (G.Adj w))).card by omega)
  obtain ⟨hxv, hxw⟩ := mem_inter.mp hx
  exact ⟨x, (mem_filter.mp hxv).1, (mem_filter.mp hxv).2.symm,
    (mem_filter.mp hxw).2.symm⟩

omit [DecidableEq V] in
lemma full_row_outside_pair_of_eighteen {t j : Finset V}
    (ht : t.card = 5) (hj : j.card = 4) (hsum : 18 ≤ contacts G t j) (x y : V) :
    ∃ z ∈ t, z ≠ x ∧ z ≠ y ∧ degreeIn G z j = 4 := by
  classical
  by_contra! hnone
  have hrows (z : V) (hz : z ∈ t) :
      degreeIn G z j ≤ 3 + (if z ∈ ({x, y} : Finset V) then 1 else 0) := by
    have hb := degreeIn_le_card G z j
    rw [hj] at hb
    split_ifs with hpair
    · omega
    · have hne : z ≠ x ∧ z ≠ y := by
        simpa only [mem_insert, mem_singleton, not_or] using hpair
      have hn := hnone z hz hne.1 hne.2
      omega
  have he : (∑ z ∈ t, if z ∈ ({x, y} : Finset V) then 1 else 0) =
      (t.filter (fun z ↦ z ∈ ({x, y} : Finset V))).card := by
    rw [card_eq_sum_ones, sum_filter]
  have hsmall : (t.filter (fun z ↦ z ∈ ({x, y} : Finset V))).card ≤ 2 :=
    (card_le_card (fun _ hz ↦ (mem_filter.mp hz).2)).trans card_le_two
  have hb := sum_le_sum hrows
  rw [sum_add_distrib, sum_const, smul_eq_mul, ht, he] at hb
  change contacts G t j ≤ 5 * 3 + _ at hb
  omega

omit [DecidableEq V] in
lemma high_row_ne_of_ten {t j : Finset V} (ht : t.card = 3) (hj : j.card = 4)
    (hsum : 10 ≤ contacts G t j) {x : V} (hx : x ∈ t) :
    ∃ y ∈ t, y ≠ x ∧ 3 ≤ degreeIn G y j := by
  classical
  by_contra! hnone
  have hlow : contacts G (t.erase x) j ≤ 4 := by
    calc
      contacts G (t.erase x) j ≤ ∑ _ ∈ t.erase x, (2 : ℕ) := by
        apply sum_le_sum
        intro y hy
        have hh := hnone y (mem_erase.mp hy).2 (mem_erase.mp hy).1
        omega
      _ = 4 := by rw [sum_const, smul_eq_mul, card_erase_of_mem hx, ht]
  have he := contacts_erase_add (G := G) (q := j) hx
  have hb := degreeIn_le_card G x j
  rw [hj] at hb
  omega

omit [DecidableRel G.Adj] in
lemma triple_third_of_two {t : Finset V} (ht : t.card = 3) {x y : V}
    (hx : x ∈ t) (hy : y ∈ t) (hxy : x ≠ y) :
    ∃ z ∈ t, x ≠ z ∧ y ≠ z ∧ t = {x, y, z} := by
  obtain ⟨z, hz, hzp⟩ := exists_mem_notMem_of_card_lt_card
    (show ({x, y} : Finset V).card < t.card by rw [card_pair hxy, ht]; decide)
  have hzne : z ≠ x ∧ z ≠ y := by
    simpa only [mem_insert, mem_singleton, not_or] using hzp
  have hsub : ({x, y, z} : Finset V) ⊆ t :=
    insert_subset hx (insert_subset hy (singleton_subset_iff.mpr hz))
  refine ⟨z, hz, hzne.1.symm, hzne.2.symm, ?_⟩
  apply (eq_of_subset_of_card_le hsub ?_).symm
  rw [card_triple_eq_three_iff.mpr ⟨hxy, hzne.1.symm, hzne.2.symm⟩, ht]

end Erdos577.FullLeafSparse
