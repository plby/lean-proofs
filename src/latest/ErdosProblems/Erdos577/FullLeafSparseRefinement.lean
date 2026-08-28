import ErdosProblems.Erdos577.FullLeafSparseFourExcluded

/-! The complete sparse-core refinement, with the actual maximum-preserving label interchange. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.type41_ordered_refinement (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type41 G p a j) (hX : degreeIn G p.leaf j = 4) :
    10 ≤ contacts G (s.erase y) j ∧
      (contacts G (s.erase y) j = 10 → 2 ≤ contacts G (s.erase y) (insert (p.vertices 3) a)) := by
  by_cases hY : degreeIn G y j = 4
  · exact hm.type41_full_marked_refinement hcard hn hj hjs hja hheavy htype hX hY
  have hj4 := (c.property.blocks_quad j hj).card
  have hYbound := degreeIn_le_card G y j
  rw [hj4] at hYbound
  have hsecond := htype.contacts_le_four hj4
  have hgreater : 11 ≤ contacts G (s.erase y) j := by
    by_contra hsmall
    have hsum := hheavy
    rw [hm.1.combined_contacts, hm.1.first_contacts, hX] at hsum
    have hfour : contacts G (insert (p.vertices 3) a) j = 4 := by omega
    exact hm.type41_four_contacts_false hcard hn hj hjs hja hheavy htype hX hfour
  constructor <;> omega

theorem Maximal.type41_refinement (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type41 G p a j) :
    G.IsNClique 4 j ∧ 10 ≤ contacts G (s.erase y) j ∧
      (contacts G (s.erase y) j = 10 → 2 ≤ contacts G (s.erase y) (insert (p.vertices 3) a)) := by
  let h := hm.1
  refine ⟨(h.type41_preparation hj hjs hheavy htype).1, ?_⟩
  by_cases hlarge : 11 ≤ contacts G (s.erase y) j
  · constructor <;> omega
  by_cases hX : degreeIn G p.leaf j = 4
  · exact hm.type41_ordered_refinement hcard hn hj hjs hja hheavy htype hX
  have hj4 := (c.property.blocks_quad j hj).card
  have hXbound := degreeIn_le_card G p.leaf j
  have hYbound := degreeIn_le_card G y j
  rw [hj4] at hXbound hYbound
  have hsecond := htype.contacts_le_four hj4
  have hY : degreeIn G y j = 4 := by
    have hsum := hheavy
    rw [h.combined_contacts, h.first_contacts] at hsum
    omega
  obtain ⟨e, q, he, _, hleaf, _, _, hthird, _, _, _, hblocks⟩ := hm.interchange hcard hn
  obtain ⟨hj', hjs', hja'⟩ := (h.swapped_outside_blocks hblocks j).mp ⟨hj, hjs, hja⟩
  have htype' : FullLeafHeavy.Type41 G q a j := by
    simpa only [FullLeafHeavy.Type41, hthird] using htype
  have hheavy' : 21 ≤ contacts G
      ((insert q.leaf (insert p.leaf (s.erase y))) ∪ insert (q.vertices 3) a) j := by
    rw [hleaf, hthird, h.first_five_swap]
    exact hheavy
  have hresult := he.type41_ordered_refinement hcard hn hj' hjs' hja' hheavy' htype'
    (by rwa [hleaf])
  simpa only [h.first_triple_swap, hthird] using hresult

end Erdos577.FullLeafCore
