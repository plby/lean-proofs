import ErdosProblems.Erdos556.BipartiteCycles
import ErdosProblems.Erdos556.ChordCycles

/-! Two elementary ways to close an odd cycle around a complete bipartite graph. -/

namespace Erdos556

open SimpleGraph Finset

theorem exists_odd_cycle_of_bipartite_side_edge {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hdis : Disjoint A B) (hA : r + 1 ≤ A.card) (hB : r ≤ B.card)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (u v : V) (hu : u ∈ A) (hv : v ∈ A) (huv : G.Adj u v) :
    ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ c.length = 2 * r + 1 := by
  obtain ⟨p, hp, hlen, _⟩ := exists_even_path_of_complete_bipartite G r hr A B
    hdis hcross hA hB u v hu hv huv.ne
  obtain ⟨c, hc, hclen⟩ := exists_cycle_of_path_and_edge p hp (by omega) huv
  exact ⟨u, c, hc, by omega⟩

theorem exists_odd_cycle_of_bipartite_outside_vertex {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hdis : Disjoint A B) (hA : r ≤ A.card) (hB : r ≤ B.card)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (x u v : V) (hxA : x ∉ A) (hxB : x ∉ B) (hu : u ∈ A) (hv : v ∈ B)
    (hxu : G.Adj x u) (hxv : G.Adj x v) :
    ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ c.length = 2 * r + 1 := by
  obtain ⟨p, hp, hlen, hsupp⟩ := exists_odd_path_of_complete_bipartite G r hr A B
    hdis hcross hA hB u v hu hv
  have hxp : x ∉ p.support := by
    intro h
    rcases mem_union.mp (hsupp x h) with h | h
    · exact hxA h
    · exact hxB h
  have hp' := hp.concat hxp hxv.symm
  obtain ⟨c, hc, hclen⟩ := exists_cycle_of_path_and_edge (p.concat hxv.symm) hp'
    (by rw [Walk.length_concat, hlen]; omega) hxu.symm
  refine ⟨u, c, hc, ?_⟩
  rw [Walk.length_concat, hlen] at hclen
  omega

#print axioms exists_odd_cycle_of_bipartite_side_edge
#print axioms exists_odd_cycle_of_bipartite_outside_vertex

end Erdos556
