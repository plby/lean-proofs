import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open Finset

/-- Minimal crossing neighbors leave an empty interval. Counting the two
disjoint neighbor sets outside that interval bounds the resulting cycle. -/
theorem exists_crossing_with_card_bound {L : ℕ} (A B : Finset ℕ)
    (hA : A ⊆ range L) (hB : B ⊆ range L) (hdisj : Disjoint A B)
    (hcross : ∃ i ∈ B, ∃ j ∈ A, i ≤ j) :
    ∃ i ∈ B, ∃ j ∈ A, i ≤ j ∧ A.card + B.card ≤ i + (L - (j + 1)) + 2 := by
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
      exact (disjoint_left.mp hdisj) (h ▸ hj) hi
    omega
  have hiL : i < L := mem_range.mp (hB hi)
  have hjL : j < L := mem_range.mp (hA hj)
  have hgap : Disjoint (A ∪ B) (Ioo i j) := by
    rw [disjoint_left]
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
  have hsub : (A ∪ B) ∪ Ioo i j ⊆ range L := by
    intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact (union_subset hA hB) ht
    · exact mem_range.mpr (lt_trans (mem_Ioo.mp ht).2 hjL)
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hgap, card_union_of_disjoint hdisj, card_range,
    Nat.card_Ioo] at hcard
  exact ⟨i, hi, j, hj, hij, by omega⟩

/-- In the noncrossing case, take the nearest endpoint-neighbors on the
two sides of a detour. The skipped gaps contain no endpoint-neighbors. -/
theorem exists_noncrossing_gap_bound {L t i j : ℕ} (A B : Finset ℕ)
    (hA : A ⊆ range L) (hB : B ⊆ range L)
    (hit : i < t) (htj : t < j) (hjL : j ≤ L)
    (hordA : ∀ z ∈ A, z < t) (hordB : ∀ z ∈ B, t ≤ z)
    (htA : t - 1 ∈ A) (htB : t ∈ B) :
    ∃ a b : ℕ, i < a ∧ a ≤ t ∧ t ≤ b ∧ b < j ∧
      a - 1 ∈ A ∧ b ∈ B ∧
      A.card + B.card ≤ i + (L - j) + (b - a) + 2 := by
  classical
  let A' := A.filter fun z ↦ i ≤ z
  let B' := B.filter fun z ↦ z < j
  have hA' : A'.Nonempty := ⟨t - 1, mem_filter.mpr ⟨htA, by omega⟩⟩
  have hB' : B'.Nonempty := ⟨t, mem_filter.mpr ⟨htB, htj⟩⟩
  obtain ⟨a, ha, hamin⟩ := A'.exists_min_image id hA'
  obtain ⟨b, hb, hbmax⟩ := B'.exists_max_image id hB'
  have haA : a ∈ A := (mem_filter.mp ha).1
  have hia : i ≤ a := (mem_filter.mp ha).2
  have hat : a < t := hordA a haA
  have hbB : b ∈ B := (mem_filter.mp hb).1
  have hbj : b < j := (mem_filter.mp hb).2
  have htb : t ≤ b := hordB b hbB
  have hAsub : A ⊆ range i ∪ Ico a t := by
    intro z hz
    by_cases hzi : z < i
    · exact mem_union.mpr (Or.inl (mem_range.mpr hzi))
    · exact mem_union.mpr (Or.inr (mem_Ico.mpr
        ⟨hamin z (mem_filter.mpr ⟨hz, by omega⟩), hordA z hz⟩))
  have hBsub : B ⊆ Icc t b ∪ Ico j L := by
    intro z hz
    by_cases hzj : z < j
    · exact mem_union.mpr (Or.inl (mem_Icc.mpr
        ⟨hordB z hz, hbmax z (mem_filter.mpr ⟨hz, hzj⟩)⟩))
    · exact mem_union.mpr (Or.inr (mem_Ico.mpr
        ⟨by omega, mem_range.mp (hB hz)⟩))
  have hcardA := (card_le_card hAsub).trans (card_union_le _ _)
  have hcardB := (card_le_card hBsub).trans (card_union_le _ _)
  rw [card_range, Nat.card_Ico] at hcardA
  rw [Nat.card_Icc, Nat.card_Ico] at hcardB
  exact ⟨a + 1, b, by omega, by omega, htb, hbj, by simpa using haA, hbB, by omega⟩

end Erdos1105

#print axioms Erdos1105.exists_crossing_with_card_bound
#print axioms Erdos1105.exists_noncrossing_gap_bound
