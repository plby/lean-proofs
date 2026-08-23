import ErdosProblems.Erdos1105.PosaCrossing

namespace Erdos1105

open SimpleGraph Finset

theorem long_path_endpoints_not_adjacent {V : Type*} {G : SimpleGraph V} {x y : V} {k : ℕ}
    (hG : NoLongCycle G k) (hk : 3 ≤ k) (p : G.Walk x y) (hp : p.IsPath)
    (hlen : k ≤ p.length + 1) : ¬G.Adj x y := by
  intro hxy
  have hcycle : (Walk.cons hxy.symm p).IsCycle := by
    apply (Walk.cons_isCycle_iff p hxy.symm).mpr
    refine ⟨hp, ?_⟩
    intro he
    have h := hp.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    omega
  have h := hG y (Walk.cons hxy.symm p) hcycle
  rw [Walk.length_cons] at h
  omega

theorem universal_mem_long_path {V : Type*} {G : SimpleGraph V} {x y u : V} {k : ℕ}
    (hG : NoLongCycle G k) (hk : 3 ≤ k) (hu : G.IsUniversal u)
    (p : G.Walk x y) (hp : p.IsPath) (hlen : k ≤ p.length + 1) : u ∈ p.support := by
  by_contra hunot
  have huy : u ≠ y := fun h ↦ hunot (h ▸ p.end_mem_support)
  have hux : u ≠ x := fun h ↦ hunot (h ▸ p.start_mem_support)
  have hdisj : p.support.Disjoint (Walk.nil : G.Walk u u).support := by
    intro z hz hz'
    have hzu : z = u := by simpa using hz'
    exact hunot (hzu ▸ hz)
  obtain ⟨q, hq, hqlen⟩ := cycle_of_two_disjoint_paths p (Walk.nil : G.Walk u u)
    hp (by simp) hdisj (hu huy).symm (hu hux) (by simp; omega)
  have h := hG u q hq
  simp only [hqlen, Walk.length_nil, add_zero] at h
  omega

/-- A common universal vertex is strictly internal to a long path. -/
theorem universal_index_internal {V : Type*} {G : SimpleGraph V} {x y u : V} {k : ℕ}
    (hG : NoLongCycle G k) (hk : 3 ≤ k) (hu : G.IsUniversal u)
    (p : G.Walk x y) (hp : p.IsPath) (hlen : k ≤ p.length + 1)
    {t : ℕ} (ht : p.getVert t = u) (htL : t ≤ p.length) : 0 < t ∧ t < p.length := by
  have hxy : x ≠ y := by
    intro h
    have hidx := hp.getVert_injOn (show 0 ≤ p.length from Nat.zero_le _)
      (show p.length ≤ p.length from le_rfl) (by simpa using h)
    omega
  have hnxy := long_path_endpoints_not_adjacent hG hk p hp hlen
  have ht0 : t ≠ 0 := by
    intro h
    have hxu : x = u := by simpa only [h, Walk.getVert_zero] using ht
    rw [← hxu] at hu
    exact hnxy (hu hxy)
  have htend : t ≠ p.length := by
    intro h
    have hyu : y = u := by simpa only [h, Walk.getVert_length] using ht
    rw [← hyu] at hu
    exact hnxy (hu hxy.symm).symm
  omega

/-- In the noncrossing case, the universal vertex separates the two
endpoint-neighbor sets along the path. -/
theorem noncrossing_neighbors_at_universal {V : Type*} {G : SimpleGraph V}
    {x y u : V} {k : ℕ} (hG : NoLongCycle G k) (hk : 3 ≤ k) (hu : G.IsUniversal u)
    (p : G.Walk x y) (hp : p.IsPath) (hlen : k ≤ p.length + 1)
    {t : ℕ} (ht : p.getVert t = u) (htL : t ≤ p.length)
    (hnoncross : ¬∃ i ∈ endNeighborIndices p, ∃ j ∈ startNeighborIndices p, i ≤ j) :
    (∀ j ∈ startNeighborIndices p, j < t) ∧ (∀ i ∈ endNeighborIndices p, t ≤ i) := by
  classical
  have htint := universal_index_internal hG hk hu p hp hlen ht htL
  have hxu : x ≠ u := by
    intro h
    have heq : p.getVert 0 = p.getVert t := by simpa only [Walk.getVert_zero, ht] using h
    have hi := hp.getVert_injOn (show 0 ≤ p.length from Nat.zero_le _) htL heq
    omega
  have hyu : y ≠ u := by
    intro h
    have heq : p.getVert p.length = p.getVert t := by
      simpa only [Walk.getVert_length, ht] using h
    have hi := hp.getVert_injOn (show p.length ≤ p.length from le_rfl) htL heq
    omega
  have htB : t ∈ endNeighborIndices p := mem_filter.mpr
    ⟨mem_range.mpr htint.2, by rw [ht]; exact (hu hyu.symm).symm⟩
  have htA : t - 1 ∈ startNeighborIndices p := by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel htint.1, ht]
    exact (hu hxu.symm).symm
  constructor
  · intro j hj
    by_contra h
    exact hnoncross ⟨t, htB, j, hj, by omega⟩
  · intro i hi
    by_contra h
    exact hnoncross ⟨i, hi, t - 1, htA, by omega⟩

end Erdos1105

#print axioms Erdos1105.universal_index_internal
