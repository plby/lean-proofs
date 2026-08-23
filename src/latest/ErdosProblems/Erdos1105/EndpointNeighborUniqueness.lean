import ErdosProblems.Erdos1105.CrossingEquality

namespace Erdos1105

open SimpleGraph Finset

/-- At equality, the end-neighbor set uniquely determines the start-neighbor
set: the interval skipped by one minimal crossing is forbidden to every
other possible start-neighbor set. -/
theorem crossing_start_set_unique {L q : ℕ} (A A' B : Finset ℕ)
    (hA : A ⊆ range L) (hA' : A' ⊆ range L) (hB : B ⊆ range L)
    (hdisj : Disjoint A B) (hdisj' : Disjoint A' B)
    (hcard : A.card + B.card = q) (hcard' : A'.card + B.card = q)
    (hcross : ∃ i ∈ B, ∃ j ∈ A, i ≤ j)
    (hbound : ∀ i ∈ B, ∀ j ∈ A, i ≤ j → i + (L - (j + 1)) + 2 ≤ q)
    (hbound' : ∀ i ∈ B, ∀ j ∈ A', i ≤ j → i + (L - (j + 1)) + 2 ≤ q) : A' = A := by
  classical
  obtain ⟨i, hi, j, hj, hij, hpart, hlen⟩ :=
    exists_crossing_partition A B hA hB hdisj hcard hcross hbound
  have hjL := mem_range.mp (hA hj)
  have hsub : A' ∪ B ⊆ A ∪ B := by
    intro t ht
    rw [hpart]
    refine mem_sdiff.mpr ⟨union_subset hA' hB ht, ?_⟩
    intro hgap
    have hit := (mem_Ioo.mp hgap).1
    have htj := (mem_Ioo.mp hgap).2
    rcases mem_union.mp ht with htA | htB
    · have := hbound' i hi t htA hit.le
      omega
    · have ht' : t ∈ range L \ Ioo i j := hpart ▸ mem_union_right A htB
      exact (mem_sdiff.mp ht').2 hgap
  have heq : A' ∪ B = A ∪ B := by
    apply eq_of_subset_of_card_le hsub
    rw [card_union_of_disjoint hdisj, card_union_of_disjoint hdisj', hcard, hcard']
  ext t
  constructor
  · intro ht
    have ht' : t ∈ A ∪ B := heq ▸ mem_union_left B ht
    exact (mem_union.mp ht').resolve_right (fun hb ↦ Finset.disjoint_left.mp hdisj' ht hb)
  · intro ht
    have ht' : t ∈ A' ∪ B := heq.symm ▸ mem_union_left B ht
    exact (mem_union.mp ht').resolve_right (fun hb ↦ Finset.disjoint_left.mp hdisj ht hb)

/-- Equal-length maximal low-core paths with the same end-neighbor positions
also have exactly the same start-neighbor positions. -/
theorem low_core_start_indices_unique {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y x' y' : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (p' : G.Walk x' y') (hp' : IsLongestSetPath (vertexCore G d : Set V) p')
    (hlen : 2 * d + 3 ≤ p.length + 1) (heqlen : p'.length = p.length)
    (hB : endNeighborIndices p' = endNeighborIndices p) :
    startNeighborIndices p' = startNeighborIndices p := by
  classical
  have hlen' : 2 * d + 3 ≤ p'.length + 1 := by omega
  have hdeg := longest_low_core_path_degrees hG hu hconn p hp hlen
  have hdeg' := longest_low_core_path_degrees hG hu hconn p' hp' hlen'
  have hdisj' := disjoint_neighbor_indices_of_no_long_cycle hG (by omega) p' hp'.isPath hlen'
  rw [hB] at hdisj'
  apply crossing_start_set_unique (startNeighborIndices p) (startNeighborIndices p')
    (endNeighborIndices p) (filter_subset _ _) (by rw [← heqlen]; exact filter_subset _ _)
    (filter_subset _ _)
    (disjoint_neighbor_indices_of_no_long_cycle hG (by omega) p hp.isPath hlen) hdisj'
    (q := 2 * d + 2)
  · rw [startNeighborIndices_card p hp.isPath, endNeighborIndices_card p hp.isPath]
    omega
  · rw [← hB, startNeighborIndices_card p' hp'.isPath, endNeighborIndices_card p' hp'.isPath]
    omega
  · exact longest_low_core_path_crossing hG hu hconn p hp hlen
  · intro i hi j hj hij
    have := crossing_chords_bound hG (by omega) p hp.isPath hi hj hij
    omega
  · intro i hi j hj hij
    rw [← hB] at hi
    have := crossing_chords_bound hG (by omega) p' hp'.isPath hi hj hij
    omega

end Erdos1105

#print axioms Erdos1105.low_core_start_indices_unique
