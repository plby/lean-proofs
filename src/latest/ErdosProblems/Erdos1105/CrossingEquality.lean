import ErdosProblems.Erdos1105.LongestCorePath

namespace Erdos1105

open SimpleGraph Finset

/-- In the equality case, a minimal crossing leaves exactly one empty
interval; all remaining positions belong to one endpoint-neighbor set. -/
theorem exists_crossing_partition {L q : ℕ} (A B : Finset ℕ)
    (hA : A ⊆ range L) (hB : B ⊆ range L) (hdisj : Disjoint A B)
    (hcard : A.card + B.card = q)
    (hcross : ∃ i ∈ B, ∃ j ∈ A, i ≤ j)
    (hbound : ∀ i ∈ B, ∀ j ∈ A, i ≤ j → i + (L - (j + 1)) + 2 ≤ q) :
    ∃ i ∈ B, ∃ j ∈ A, i < j ∧
      A ∪ B = range L \ Ioo i j ∧ i + (L - (j + 1)) + 2 = q := by
  classical
  let P := (B ×ˢ A).filter fun p ↦ p.1 ≤ p.2
  have hP : P.Nonempty := by
    obtain ⟨i, hi, j, hj, hij⟩ := hcross
    exact ⟨(i, j), mem_filter.mpr ⟨mem_product.mpr ⟨hi, hj⟩, hij⟩⟩
  obtain ⟨⟨i, j⟩, hp, hmin⟩ := P.exists_min_image (fun p ↦ p.2 - p.1) hP
  have hi : i ∈ B := (mem_product.mp (mem_filter.mp hp).1).1
  have hj : j ∈ A := (mem_product.mp (mem_filter.mp hp).1).2
  have hij : i ≤ j := (mem_filter.mp hp).2
  have hij' : i < j := by
    have hne : i ≠ j := by
      intro h
      exact (Finset.disjoint_left.mp hdisj) (h ▸ hj) hi
    omega
  have hjL : j < L := mem_range.mp (hA hj)
  have hgap : Disjoint (A ∪ B) (Ioo i j) := by
    rw [Finset.disjoint_left]
    intro t ht hti
    have hit : i < t := (mem_Ioo.mp hti).1
    have htj : t < j := (mem_Ioo.mp hti).2
    rcases mem_union.mp ht with htA | htB
    · have hh := hmin (i, t) (mem_filter.mpr ⟨mem_product.mpr ⟨hi, htA⟩, hit.le⟩)
      dsimp at hh
      omega
    · have hh := hmin (t, j) (mem_filter.mpr ⟨mem_product.mpr ⟨htB, hj⟩, htj.le⟩)
      dsimp at hh
      omega
  have hgapSub : Ioo i j ⊆ range L := by
    intro t ht
    exact mem_range.mpr ((mem_Ioo.mp ht).2.trans hjL)
  have hsub : A ∪ B ⊆ range L \ Ioo i j := by
    intro t ht
    exact mem_sdiff.mpr ⟨union_subset hA hB ht,
      fun h ↦ Finset.disjoint_left.mp hgap ht h⟩
  have hc := card_le_card hsub
  have hright : (range L \ Ioo i j).card = L - (j - i - 1) := by
    rw [card_sdiff_of_subset hgapSub, card_range, Nat.card_Ioo]
  rw [card_union_of_disjoint hdisj, hcard, hright] at hc
  have hb := hbound i hi j hj hij
  have hceq : (range L \ Ioo i j).card = (A ∪ B).card := by
    rw [hright, card_union_of_disjoint hdisj, hcard]
    omega
  exact ⟨i, hi, j, hj, hij', eq_of_subset_of_card_le hsub hceq.le, by omega⟩

/-- The low-core endpoint-neighbor sets realize the equality partition. -/
theorem longest_low_core_crossing_partition {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : 2 * d + 3 ≤ p.length + 1) :
    ∃ i ∈ endNeighborIndices p, ∃ j ∈ startNeighborIndices p, i < j ∧
      startNeighborIndices p ∪ endNeighborIndices p = range p.length \ Ioo i j ∧
      i + (p.length - (j + 1)) + 2 = 2 * d + 2 := by
  have hdeg := longest_low_core_path_degrees hG hu hconn p hp hlen
  apply exists_crossing_partition (startNeighborIndices p) (endNeighborIndices p)
    (by classical exact filter_subset _ _) (by classical exact filter_subset _ _)
    (disjoint_neighbor_indices_of_no_long_cycle hG (by omega) p hp.isPath hlen)
  · rw [startNeighborIndices_card p hp.isPath, endNeighborIndices_card p hp.isPath]
    omega
  · exact longest_low_core_path_crossing hG hu hconn p hp hlen
  · intro i hi j hj hij
    have := crossing_chords_bound hG (by omega) p hp.isPath hi hj hij
    omega

end Erdos1105

#print axioms Erdos1105.longest_low_core_crossing_partition
