import ErdosProblems.Erdos1105.CrossingEquality
import ErdosProblems.Erdos1105.PosaRotation

namespace Erdos1105

open SimpleGraph Finset

/-- Before the first end-neighbor, every shifted position belongs to
the start-neighbor set of a long low-core path. -/
theorem low_core_start_neighbors_before {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : 2 * d + 3 ≤ p.length + 1) {a : ℕ} (ha : a ≤ p.length)
    (hbefore : ∀ j < a, ¬G.Adj y (p.getVert j)) :
    ∀ j < a, G.Adj x (p.getVert (j + 1)) := by
  classical
  obtain ⟨i, hi, j, hj, hij, hpart, _⟩ :=
    longest_low_core_crossing_partition hG hu hconn p hp hlen
  have hai : a ≤ i := by
    by_contra hn
    exact hbefore i (by omega) (mem_filter.mp hi).2
  intro r hr
  have hm : r ∈ startNeighborIndices p ∪ endNeighborIndices p := by
    rw [hpart]
    exact mem_sdiff.mpr ⟨mem_range.mpr (by omega), fun h ↦ by
      have := (mem_Ioo.mp h).1
      omega⟩
  rcases mem_union.mp hm with h | h
  · exact (mem_filter.mp h).2
  · exact (hbefore r hr (mem_filter.mp h).2).elim

/-- Rotations entirely before the first end-neighbor show that this
initial segment is a clique, joined to the next vertex of the path. -/
theorem low_core_initial_segment_clique {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : 2 * d + 3 ≤ p.length + 1) {a : ℕ} (ha : a ≤ p.length)
    (hbefore : ∀ j < a, ¬G.Adj y (p.getVert j)) :
    ∀ r < a, ∀ s ≤ a, r ≠ s → G.Adj (p.getVert r) (p.getVert s) := by
  classical
  have hstart := low_core_start_neighbors_before hG hu hconn p hp hlen ha hbefore
  have hcore := (longest_low_core_path_neighbors hG hu hconn p hp hlen).1
  intro r hr s hs hrs
  have hrL : r < p.length := by omega
  have hrmem : p.getVert r ∈ vertexCore G d := by
    by_cases hr0 : r = 0
    · simpa only [hr0, Walk.getVert_zero, Finset.mem_coe] using hp.left_mem
    · apply hcore _ (p.getVert_mem_support r)
      have h := hstart (r - 1) (by omega)
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ r)] at h
  let q := posaRotateStart p r (hstart r hr)
  have hq := hp.posaRotateStart hrL (hstart r hr) hrmem
  have hqlen : q.length = p.length := posaRotateStart_length p hrL (hstart r hr)
  have hqbefore : ∀ j < a, ¬G.Adj y (q.getVert j) := by
    intro j hj
    by_cases hjr : j ≤ r
    · rw [posaRotateStart_getVert_prefix p hrL (hstart r hr) hjr]
      exact hbefore (r - j) (by omega)
    · rw [posaRotateStart_getVert_suffix p hrL (hstart r hr) (by omega : r < j)]
      exact hbefore j hj
  have hqstart := low_core_start_neighbors_before hG hu hconn q hq
    (by omega) (show a ≤ q.length by omega) hqbefore
  by_cases hsr : s < r
  · have h := hqstart (r - s - 1) (by omega)
    have heq : r - s - 1 + 1 = r - s := by omega
    rw [heq, posaRotateStart_getVert_prefix p hrL (hstart r hr) (Nat.sub_le r s)] at h
    rwa [Nat.sub_sub_self hsr.le] at h
  · have hrs' : r < s := by omega
    have h := hqstart (s - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ s),
      posaRotateStart_getVert_suffix p hrL (hstart r hr) hrs'] at h
    exact h

end Erdos1105

#print axioms Erdos1105.low_core_initial_segment_clique
