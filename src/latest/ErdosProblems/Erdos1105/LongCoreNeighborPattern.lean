import ErdosProblems.Erdos1105.LowCoreEndpointData

namespace Erdos1105

open SimpleGraph Finset

/-- When a maximal low-core path has more than the forbidden cycle
order, its endpoint-neighbor pattern has just two common attachment
vertices, with cliques of size `d` at the two ends. -/
theorem long_low_core_neighbor_pattern {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : 2 * d + 3 ≤ p.length) :
    startNeighborIndices p = insert (p.length - d - 1) (range d) ∧
      endNeighborIndices p = insert d (Ico (p.length - d) p.length) := by
  classical
  have hlong : 2 * d + 3 ≤ p.length + 1 := by omega
  obtain ⟨a, b, ha0, hab, hbL, hya, hxb, hbefore, hafter, hnoA, hnoB⟩ :=
    low_core_endpoint_data hG hu hconn p hp hlong
  obtain ⟨i, hi, j, hj, hij, hpart, hcut⟩ :=
    longest_low_core_crossing_partition hG hu hconn p hp hlong
  have hiL : i < p.length := mem_range.mp (mem_filter.mp hi).1
  have hjL : j < p.length := mem_range.mp (mem_filter.mp hj).1
  have hai : a ≤ i := by
    by_contra h
    exact hbefore i (by omega) (mem_filter.mp hi).2
  have hjb : j + 1 ≤ b := by
    by_contra h
    exact hafter (j + 1) (by omega) (by omega) (mem_filter.mp hj).2
  have hcover (t : ℕ) (ht : t < p.length) (hgap : ¬(i < t ∧ t < j)) :
      t ∈ startNeighborIndices p ∨ t ∈ endNeighborIndices p := by
    apply mem_union.mp
    rw [hpart]
    exact mem_sdiff.mpr ⟨mem_range.mpr ht, fun h ↦ hgap (mem_Ioo.mp h)⟩
  have hia : i = a := by
    by_contra hne
    have hai' : a < i := by omega
    rcases hcover (a + 1) (by omega) (by omega) with hA | hB
    · have haB : a ∈ endNeighborIndices p :=
        mem_filter.mpr ⟨mem_range.mpr (by omega), hya⟩
      have hc := crossing_chords_bound hG (by omega) p hp.isPath haB hA (by omega)
      omega
    · exact hnoB a hab ⟨hya, (mem_filter.mp hB).2⟩
  have hjb' : j + 1 = b := by
    by_contra hne
    have hjb' : j + 1 < b := by omega
    rcases hcover (b - 2) (by omega) (by omega) with hA | hB
    · have hadj : G.Adj x (p.getVert (b - 1)) := by
        have h := (mem_filter.mp hA).2
        have heq : b - 2 + 1 = b - 1 := by omega
        rwa [heq] at h
      have hadj' : G.Adj x (p.getVert (b - 1 + 1)) := by
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ b)]
      exact hnoA (b - 1) (by omega) (by omega) ⟨hadj, hadj'⟩
    · have hbA : b - 1 ∈ startNeighborIndices p := by
        apply mem_filter.mpr
        refine ⟨mem_range.mpr (by omega), ?_⟩
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ b)]
      have hc := crossing_chords_bound hG (by omega) p hp.isPath hB hbA (by omega)
      omega
  have hstart := low_core_start_neighbors_before hG hu hconn p hp hlong
    (show a ≤ p.length by omega) hbefore
  have hdisj := disjoint_neighbor_indices_of_no_long_cycle hG (by omega) p hp.isPath hlong
  have hAeq : startNeighborIndices p = insert j (range a) := by
    ext t
    constructor
    · intro ht
      apply mem_insert.mpr
      by_cases htj : t = j
      · exact Or.inl htj
      · apply Or.inr
        apply mem_range.mpr
        have htL := mem_range.mp (mem_filter.mp ht).1
        have htb : t + 1 ≤ b := by
          by_contra h
          exact hafter (t + 1) (by omega) (by omega) (mem_filter.mp ht).2
        have hnotgap : ¬(i < t ∧ t < j) := by
          have hm : t ∈ range p.length \ Ioo i j := hpart ▸ mem_union_left _ ht
          exact fun h ↦ (mem_sdiff.mp hm).2 (mem_Ioo.mpr h)
        have hti : t ≠ i := fun h ↦ Finset.disjoint_left.mp hdisj (h ▸ ht) hi
        omega
    · intro ht
      rcases mem_insert.mp ht with h | h
      · exact h ▸ hj
      · exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp h; omega),
          hstart t (mem_range.mp h)⟩
  have hAcard : (startNeighborIndices p).card = d + 1 := by
    rw [startNeighborIndices_card p hp.isPath]
    exact (longest_low_core_path_degrees hG hu hconn p hp hlong).2.2.1
  have had : a = d := by
    rw [hAeq, card_insert_of_notMem (by simp only [mem_range]; omega), card_range] at hAcard
    omega
  have hb : b = p.length - d := by omega
  have hj' : j = p.length - d - 1 := by omega
  refine ⟨by simpa only [had, hj'] using hAeq, ?_⟩
  have hBeq : endNeighborIndices p = insert a (Ico b p.length) := by
    ext t
    constructor
    · intro ht
      apply mem_insert.mpr
      by_cases hta : t = a
      · exact Or.inl hta
      · apply Or.inr
        have htL := mem_range.mp (mem_filter.mp ht).1
        have hat : a ≤ t := by
          by_contra h
          exact hbefore t (by omega) (mem_filter.mp ht).2
        have hnotgap : ¬(i < t ∧ t < j) := by
          have hm : t ∈ range p.length \ Ioo i j := hpart ▸ mem_union_right _ ht
          exact fun h ↦ (mem_sdiff.mp hm).2 (mem_Ioo.mpr h)
        have htj : t ≠ j := fun h ↦ Finset.disjoint_left.mp hdisj hj (h ▸ ht)
        exact mem_Ico.mpr ⟨by omega, htL⟩
    · intro ht
      rcases mem_insert.mp ht with h | h
      · exact h ▸ (hia ▸ hi)
      · have hbt := (mem_Ico.mp h).1
        have htL := (mem_Ico.mp h).2
        rcases hcover t htL (by omega) with htA | htB
        · exact (hafter (t + 1) (by omega) (by omega) (mem_filter.mp htA).2).elim
        · exact htB
  simpa only [had, hb] using hBeq

end Erdos1105

#print axioms Erdos1105.long_low_core_neighbor_pattern
