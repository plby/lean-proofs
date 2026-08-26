import ErdosProblems.Erdos556.DenseBipartitePaths
import ErdosProblems.Erdos556.ChordCycles

/-! Odd-cycle consequences of a dense bipartite pair. -/

namespace Erdos556

open SimpleGraph Finset

theorem no_side_edges_of_forbidden_odd_cycle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) (r d : ℕ) (hr : 1 ≤ r)
    (hdis : Disjoint X Y) (hdef : BipartiteDefect G X Y d)
    (hX : r + 2 * d + 1 ≤ X.card) (hY : r + 2 * d ≤ Y.card)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ G) :
    ∀ u ∈ X, ∀ v ∈ X, ¬ G.Adj u v := by
  intro u hu v hv huv
  obtain ⟨p, hp, hlen, _⟩ := exists_even_path_of_bipartite_defect G r d hr X Y hdis hdef hX hY
    u v hu hv huv.ne
  obtain ⟨c, hc, hclen⟩ := exists_cycle_of_path_and_edge p hp (by omega) huv
  exact hno ((cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr ⟨u, c, hc, by omega⟩)

theorem outside_vertex_not_adjacent_to_both_sides {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) (r d : ℕ) (hr : 2 ≤ r)
    (hdis : Disjoint X Y) (hdef : BipartiteDefect G X Y d)
    (hX : r + 2 * d ≤ X.card) (hY : r + 2 * d ≤ Y.card)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ G)
    (x : V) (hxX : x ∉ X) (hxY : x ∉ Y)
    (u v : V) (hu : u ∈ X) (hv : v ∈ Y) : ¬ (G.Adj x u ∧ G.Adj x v) := by
  rintro ⟨hxu, hxv⟩
  obtain ⟨p, hp, hlen, hsupp⟩ := exists_odd_path_of_bipartite_defect G r d hr X Y hdis hdef hX hY
    u v hu hv
  have hxp : x ∉ p.support := by
    intro h
    rcases mem_union.mp (hsupp x h) with h | h
    · exact hxX h
    · exact hxY h
  obtain ⟨c, hc, hclen⟩ := exists_cycle_of_path_and_edge (p.concat hxv.symm)
    (hp.concat hxp hxv.symm) (by rw [Walk.length_concat, hlen]; omega) hxu.symm
  have hclen' : c.length = 2 * r + 1 := by
    rw [Walk.length_concat, hlen] at hclen
    omega
  exact hno ((cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr ⟨u, c, hc, hclen'⟩)

#print axioms no_side_edges_of_forbidden_odd_cycle
#print axioms outside_vertex_not_adjacent_to_both_sides

end Erdos556
