import ErdosProblems.Erdos1105.LowCoreNoConsecutive

namespace Erdos1105

open SimpleGraph Finset

/-- The first end-neighbor and last start-neighbor delimit the alternating
middle of a maximal low-core path. -/
theorem low_core_endpoint_data {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : 2 * d + 3 ≤ p.length + 1) :
    ∃ a b : ℕ, 1 ≤ a ∧ a < b ∧ b < p.length ∧
      G.Adj y (p.getVert a) ∧ G.Adj x (p.getVert b) ∧
      (∀ j < a, ¬G.Adj y (p.getVert j)) ∧
      (∀ j, b < j → j ≤ p.length → ¬G.Adj x (p.getVert j)) ∧
      (∀ t, a ≤ t → t < p.length →
        ¬(G.Adj x (p.getVert t) ∧ G.Adj x (p.getVert (t + 1)))) ∧
      (∀ t < b, ¬(G.Adj y (p.getVert t) ∧ G.Adj y (p.getVert (t + 1)))) := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ := longest_low_core_path_crossing hG hu hconn p hp hlen
  obtain ⟨a, ha, hamin⟩ := (endNeighborIndices p).exists_min_image id ⟨i, hi⟩
  obtain ⟨b₀, hb₀, hbmax⟩ := (startNeighborIndices p).exists_max_image id ⟨j, hj⟩
  let b := b₀ + 1
  have haL : a < p.length := mem_range.mp (mem_filter.mp ha).1
  have hbL : b ≤ p.length := by
    have := mem_range.mp (mem_filter.mp hb₀).1
    dsimp [b]
    omega
  have hay : G.Adj y (p.getVert a) := (mem_filter.mp ha).2
  have hbx : G.Adj x (p.getVert b) := (mem_filter.mp hb₀).2
  have hnxy := long_path_endpoints_not_adjacent hG (by omega) p hp.isPath hlen
  have ha0 : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    exact hnxy (by simpa only [ha0, Walk.getVert_zero] using hay.symm)
  have hbLt : b < p.length := by
    by_contra h
    have hbeq : b = p.length := by omega
    exact hnxy (by simpa only [hbeq, Walk.getVert_length] using hbx)
  have hab : a < b := by
    have := hamin i hi
    have := hbmax j hj
    dsimp only [id, b] at *
    omega
  have hbefore : ∀ r < a, ¬G.Adj y (p.getVert r) := by
    intro r hr hadj
    have := hamin r (mem_filter.mpr ⟨mem_range.mpr (by omega), hadj⟩)
    dsimp only [id] at this
    omega
  have hafter : ∀ r, b < r → r ≤ p.length → ¬G.Adj x (p.getVert r) := by
    intro r hr hrL hadj
    have hmem : r - 1 ∈ startNeighborIndices p := by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by omega), ?_⟩
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ r)]
    have := hbmax (r - 1) hmem
    dsimp only [id, b] at *
    omega
  refine ⟨a, b, ha0, hab, hbLt, hay, hbx, hbefore, hafter, ?_, ?_⟩
  · intro t hat ht
    exact low_core_no_consecutive_start_neighbors hG hu hconn p hp hlen ha0 haL.le
      hay hbefore hat ht
  · intro t ht
    exact low_core_no_consecutive_end_neighbors hG hu hconn p hp hlen hbLt hbx hafter ht

end Erdos1105

#print axioms Erdos1105.low_core_endpoint_data
