import ErdosProblems.Erdos577.FullLeafSixHighPreparation

/-! Apart from a zero second side, a high first row leaves only the eight-plus-four case. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.first_nine_second_zero (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    {u : V} (hu : u ∈ s.erase y) (hrow : 3 ≤ degreeIn G u j)
    (hfirst : 9 ≤ contacts G (s.erase y) j) :
    contacts G (FullLeafEquality.matchedSecond p s a y) j = 0 := by
  have huFirst : u ∈ insert p.leaf s := mem_insert_of_mem (mem_erase.mp hu).2
  have hedges := h.first_high_edges hj hjs huFirst hrow
  have hrep := h.first_universal_replacements huFirst hj hjs hrow
  apply sum_eq_zero
  intro v hv
  by_contra hne
  have hpos : 1 ≤ degreeIn G v j := by omega
  obtain ⟨hvSecond, hvPositive⟩ := mem_filter.mp hv
  have hvout : v ∉ s.erase y := fun hh ↦
    disjoint_left.mp h.matched_triples_disjoint hh hv
  obtain ⟨q, hleaf, htriangle⟩ := Paw.exists_of_triangle h.first_triple_clique hvout hvPositive
  have hsupport : q.support = insert v (s.erase y) := by rw [q.support_eq, hleaf, htriangle]
  obtain ⟨w, hw⟩ := c.property.blocks_quad j hj
  have hdis : Disjoint q.support w.support := by
    rw [hsupport, hw]
    exact disjoint_insert_left.mpr
      ⟨fun hh ↦ disjoint_left.mp (h.matched_second_disjoint_block hj hja) hv hh,
        (h.five_disjoint_block hj hjs).mono_left
          (fun z hz ↦ mem_insert_of_mem (mem_erase.mp hz).2)⟩
  have hf := q.nine_triangle_universal_factor w hdis (by rwa [hleaf, hw])
    (by rwa [htriangle, hw]) (by rwa [hw]) (by
      refine ⟨u, htriangle.symm ▸ hu, ?_⟩
      simpa only [hw] using hrep)
  rw [hsupport, hw, insert_union] at hf
  exact h.second_no_factor hcard hn hvSecond hj hjs hja hf

theorem Configuration.high_first_rows_alternative (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (htotal : 12 ≤ contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) j)
    {u : V} (hu : u ∈ s.erase y) (hrow : 3 ≤ degreeIn G u j) :
    contacts G (FullLeafEquality.matchedSecond p s a y) j = 0 ∨
      (contacts G (s.erase y) j = 8 ∧
        contacts G (FullLeafEquality.matchedSecond p s a y) j = 4) := by
  by_cases hfirst : 9 ≤ contacts G (s.erase y) j
  · exact Or.inl (h.first_nine_second_zero hcard hn hj hjs hja hu hrow hfirst)
  · have hsecond := h.high_first_matched_contacts_le_four hcard hn hj hjs hja
      (mem_insert_of_mem (mem_erase.mp hu).2) hrow
    rw [contacts_union_left G h.matched_triples_disjoint] at htotal
    exact Or.inr ⟨by omega, by omega⟩

end Erdos577.FullLeafCore
