import ErdosProblems.Erdos1105.CrossingEquality
import ErdosProblems.Erdos1105.PosaRotation

namespace Erdos1105

open SimpleGraph Finset

/-- For a low-core path with exactly the forbidden cycle order, the
shifted endpoint-neighbor sets partition all path-edge positions. -/
theorem short_low_core_neighbor_partition {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : p.length = 2 * d + 2) :
    startNeighborIndices p ∪ endNeighborIndices p = range p.length := by
  classical
  have hlong : 2 * d + 3 ≤ p.length + 1 := by omega
  have hdeg := longest_low_core_path_degrees hG hu hconn p hp hlong
  have hdisj := disjoint_neighbor_indices_of_no_long_cycle hG (by omega) p hp.isPath hlong
  have hsub : startNeighborIndices p ∪ endNeighborIndices p ⊆ range p.length :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  apply eq_of_subset_of_card_le hsub
  rw [card_union_of_disjoint hdisj, card_range,
    startNeighborIndices_card p hp.isPath, endNeighborIndices_card p hp.isPath]
  omega

/-- In the short equality case, one endpoint's neighbors determine
the other endpoint's neighbors exactly. -/
theorem short_low_core_neighbor_iff {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : p.length = 2 * d + 2) {i : ℕ} (hi : i < p.length) :
    G.Adj x (p.getVert (i + 1)) ↔ ¬G.Adj y (p.getVert i) := by
  classical
  have hpart := short_low_core_neighbor_partition hG hu hconn p hp hlen
  have hdisj := disjoint_neighbor_indices_of_no_long_cycle hG (by omega) p hp.isPath
    (by omega : 2 * d + 3 ≤ p.length + 1)
  constructor
  · intro hx hy
    exact Finset.disjoint_left.mp hdisj
      (mem_filter.mpr ⟨mem_range.mpr hi, hx⟩) (mem_filter.mpr ⟨mem_range.mpr hi, hy⟩)
  · intro hny
    have hm : i ∈ startNeighborIndices p ∪ endNeighborIndices p := hpart ▸ mem_range.mpr hi
    rcases mem_union.mp hm with hx | hy
    · exact (mem_filter.mp hx).2
    · exact (hny (mem_filter.mp hy).2).elim

end Erdos1105

#print axioms Erdos1105.short_low_core_neighbor_iff
