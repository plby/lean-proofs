import ErdosProblems.Erdos556.ThreeColourTools
import ErdosProblems.Erdos556.DenseBipartitePaths
import ErdosProblems.Erdos556.BipartiteOddCycle
import ErdosProblems.Erdos556.OutsidePathBridge

/-! The mixed red-blue outside-vertex configuration in the first four-core pattern. -/

namespace Erdos556

open SimpleGraph Finset

theorem monochromatic_cycle_of_mixed_four_core_neighbors {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (A : Fin 4 → Finset V) (r d : ℕ) (hr : 4 ≤ r)
    (hdis : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hsize : ∀ i, r + 2 * d + 1 ≤ (A i).card)
    (hred02 : BipartiteDefect (c.graph 0) (A 0) (A 2) d)
    (hred13 : BipartiteDefect (c.graph 0) (A 1) (A 3) d)
    (hdiag : ∀ b ∈ A 1, ∀ z ∈ A 2, ¬ (c.graph 2).Adj b z)
    (x : V) (hx : ∀ i, x ∉ A i) (u : Fin 4 → V) (hu : ∀ i, u i ∈ A i)
    (h0 : (c.graph 0).Adj x (u 0)) (h3 : (c.graph 0).Adj x (u 3))
    (h1 : (c.graph 1).Adj x (u 1)) (h2 : (c.graph 1).Adj x (u 2)) :
    cycleGraph (2 * r + 1) ⊑ c.graph 0 ∨ cycleGraph (2 * r + 1) ⊑ c.graph 1 := by
  classical
  by_cases hex : ∃ b ∈ A 1, ∃ z ∈ A 2, (c.graph 0).Adj b z
  · obtain ⟨b, hb, z, hz, hbz⟩ := hex
    obtain ⟨p, hp, hplen, hpS⟩ := exists_odd_path_of_bipartite_defect (c.graph 0) (r - 2) d
      (by omega) (A 0) (A 2) (hdis 0 2 (by decide)) hred02
      (by have h := hsize 0; omega) (by have h := hsize 2; omega) (u 0) z (hu 0) hz
    obtain ⟨q, hq, hqlen, hqS⟩ := exists_odd_path_of_bipartite_defect (c.graph 0) 2 d
      (by decide) (A 1) (A 3) (hdis 1 3 (by decide)) hred13
      (by have h := hsize 1; omega) (by have h := hsize 3; omega) b (u 3) hb (hu 3)
    have hXY : Disjoint (A 0 ∪ A 2) (A 1 ∪ A 3) := by
      rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨hdis 0 1 (by decide), hdis 0 3 (by decide)⟩,
        ⟨hdis 2 1 (by decide), hdis 2 3 (by decide)⟩⟩
    have hxX : x ∉ A 0 ∪ A 2 := by simp only [mem_union, not_or]; exact ⟨hx 0, hx 2⟩
    have hxY : x ∉ A 1 ∪ A 3 := by simp only [mem_union, not_or]; exact ⟨hx 1, hx 3⟩
    obtain ⟨v, w, hw, hwlen⟩ := exists_cycle_of_two_paths_and_outside_vertex
      (A 0 ∪ A 2) (A 1 ∪ A 3) hXY hxX hxY (mem_union_left _ hb) p q hp hq
      (by omega) hpS hqS h0 h3 hbz.symm
    left
    exact (cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr ⟨v, w, hw, by omega⟩
  · have hblue : ∀ b ∈ A 1, ∀ z ∈ A 2, (c.graph 1).Adj b z := by
      intro b hb z hz
      have hbzne : b ≠ z := fun h => (Finset.disjoint_left.mp (hdis 1 2 (by decide)) hb) (h ▸ hz)
      rcases fin_three_cases (c.colour b z) with h | h | h
      · exact (hex ⟨b, hb, z, hz, ⟨hbzne, h⟩⟩).elim
      · exact ⟨hbzne, h⟩
      · exact (hdiag b hb z hz ⟨hbzne, h⟩).elim
    right
    exact (cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr
      (exists_odd_cycle_of_bipartite_outside_vertex (c.graph 1) (A 1) (A 2) r (by omega)
        (hdis 1 2 (by decide)) (by have h := hsize 1; omega) (by have h := hsize 2; omega)
        hblue x (u 1) (u 2) (hx 1) (hx 2) (hu 1) (hu 2) h1 h2)

#print axioms monochromatic_cycle_of_mixed_four_core_neighbors

end Erdos556
