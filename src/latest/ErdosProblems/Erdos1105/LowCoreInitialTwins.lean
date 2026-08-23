import ErdosProblems.Erdos1105.LowCoreInitialClique
import ErdosProblems.Erdos1105.EndpointNeighborUniqueness

namespace Erdos1105

open SimpleGraph Finset

lemma posaRotateStart_end_indices {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) {i : ℕ} (hi : i < p.length)
    (h : G.Adj x (p.getVert (i + 1)))
    (hbefore : ∀ j ≤ i, ¬G.Adj y (p.getVert j)) :
    endNeighborIndices (posaRotateStart p i h) = endNeighborIndices p := by
  classical
  ext j
  simp only [endNeighborIndices, mem_filter, mem_range, posaRotateStart_length p hi h]
  by_cases hj : j ≤ i
  · rw [posaRotateStart_getVert_prefix p hi h hj]
    simp only [hbefore (i - j) (Nat.sub_le i j), hbefore j hj, and_false]
  · rw [posaRotateStart_getVert_suffix p hi h (by omega : i < j)]

/-- All vertices before the first end-neighbor have the same neighbors
on the remaining part of a maximal low-core path. -/
theorem low_core_initial_segment_twins {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : 2 * d + 3 ≤ p.length + 1) {a : ℕ} (ha : a ≤ p.length)
    (hbefore : ∀ j < a, ¬G.Adj y (p.getVert j)) :
    ∀ r < a, ∀ s, a ≤ s → s ≤ p.length →
      (G.Adj (p.getVert r) (p.getVert s) ↔ G.Adj x (p.getVert s)) := by
  classical
  have hstart := low_core_start_neighbors_before hG hu hconn p hp hlen ha hbefore
  have hcore := (longest_low_core_path_neighbors hG hu hconn p hp hlen).1
  intro r hr s has hs
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
  have hB : endNeighborIndices q = endNeighborIndices p :=
    posaRotateStart_end_indices p hrL (hstart r hr) (fun j hj ↦ hbefore j (by omega))
  have hA := low_core_start_indices_unique hG hu hconn p hp q hq hlen hqlen hB
  have hiff : s - 1 ∈ startNeighborIndices q ↔ s - 1 ∈ startNeighborIndices p := by rw [hA]
  simp only [startNeighborIndices, mem_filter, mem_range, hqlen,
    show s - 1 < p.length by omega, true_and, Nat.sub_add_cancel (by omega : 1 ≤ s)] at hiff
  rwa [posaRotateStart_getVert_suffix p hrL (hstart r hr) (by omega : r < s)] at hiff

end Erdos1105

#print axioms Erdos1105.low_core_initial_segment_twins
