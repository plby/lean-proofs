import ErdosProblems.Erdos421.EqualDescendants
import ErdosProblems.Erdos421.WitnessLengths

/-! # The rejection forest with an arbitrary absolute gap-length cutoff -/

namespace Erdos421

theorem EqualEdge.parent_gap_lt {i k : ℕ} (h : EqualEdge i k) : gapLength i < gapLength k := by
  obtain ⟨j, hj, hL, hR⟩ := h
  have hlen : j * gapLength i < gapLength k :=
    equal_edge_length (prime_strictMono (Nat.lt_succ_self i)).le hL hR
  nlinarith

theorem ParentData.bounded_edge_alternatives {k B H : ℕ} (w : ParentData k)
    (hB : prime (k + 1) ≤ B) (hH : gapLength k ≤ H) :
    EqualEdge w.index k ∨ (prime w.index) ^ 2 ≤
      B * gapLength w.index + prime w.index * H := by
  rcases witness_boundary_alternatives w.left_mem w.right_mem w.witness.separated
      w.witness.product_eq with heq | hineq
  · obtain ⟨j, hj, hL, hR⟩ := heq
    exact Or.inl ⟨j, hj, w.witness.gap_left.trans_le hL, hR.trans_lt w.witness.gap_right⟩
  · right
    have hn : w.witness.n ≤ B := w.witness.gap_right.le.trans hB
    have hs : w.witness.n - w.witness.m + 1 ≤ H := w.witness.laterLength_le_gap.trans hH
    exact hineq.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hn) (Nat.mul_le_mul_left _ hs))

theorem parent_bounded_edge_alternatives {k B H : ℕ} (hk : Rejected k) (hraw : ¬ Raw k)
    (hB : prime (k + 1) ≤ B) (hH : gapLength k ≤ H) :
    EqualEdge (parent k) k ∨ (prime (parent k)) ^ 2 ≤
      B * gapLength (parent k) + prime (parent k) * H := by
  classical
  have h : Rejected k ∧ ¬ Raw k := ⟨hk, hraw⟩
  simp only [parent, dif_pos h]
  exact (chosenParentData k h).bounded_edge_alternatives hB hH

noncomputable def boundedRejections (B H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range B).filter (fun k ↦ Rejected k ∧ prime (k + 1) ≤ B ∧ gapLength k ≤ H)

theorem mem_boundedRejections {B H k : ℕ} : k ∈ boundedRejections B H ↔
    Rejected k ∧ prime (k + 1) ≤ B ∧ gapLength k ≤ H := by
  classical
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    have hidx : k + 1 ≤ prime (k + 1) := prime_strictMono.id_le (k + 1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hidx.trans hk.2.1), hk⟩

noncomputable def boundedRaw (B H : ℕ) : Finset ℕ := by
  classical
  exact (boundedRejections B H).filter Raw

theorem mem_boundedRaw {B H k : ℕ} : k ∈ boundedRaw B H ↔
    Raw k ∧ prime (k + 1) ≤ B ∧ gapLength k ≤ H := by
  classical
  simp only [boundedRaw, Finset.mem_filter, mem_boundedRejections]
  constructor
  · rintro ⟨⟨_, hB, hH⟩, hr⟩
    exact ⟨hr, hB, hH⟩
  · rintro ⟨hr, hB, hH⟩
    exact ⟨⟨hr.1, hB, hH⟩, hr⟩

noncomputable def boundedChildren (B H i : ℕ) : Finset ℕ := by
  classical
  exact (boundedRejections B H).filter (fun k ↦ ¬ Raw k ∧ parent k = i)

theorem mem_boundedChildren {B H i k : ℕ} : k ∈ boundedChildren B H i ↔
    Rejected k ∧ ¬ Raw k ∧ prime (k + 1) ≤ B ∧ gapLength k ≤ H ∧ parent k = i := by
  classical
  simp only [boundedChildren, Finset.mem_filter, mem_boundedRejections]
  tauto

noncomputable def boundedEqualDescendants (B H i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range B).filter
    (fun k ↦ prime (k + 1) ≤ B ∧ gapLength k ≤ H ∧ (k = i ∨ EqualEdge i k))

theorem mem_boundedEqualDescendants {B H i k : ℕ} : k ∈ boundedEqualDescendants B H i ↔
    prime (k + 1) ≤ B ∧ gapLength k ≤ H ∧ (k = i ∨ EqualEdge i k) := by
  classical
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    have hidx : k + 1 ≤ prime (k + 1) := prime_strictMono.id_le (k + 1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hidx.trans hk.1), hk⟩

noncomputable def boundedSeeds (B H : ℕ) : Finset ℕ := by
  classical
  exact (boundedRejections B H).filter (fun k ↦ Raw k ∨ ¬ EqualEdge (parent k) k)

theorem mem_boundedSeeds {B H k : ℕ} : k ∈ boundedSeeds B H ↔
    Rejected k ∧ prime (k + 1) ≤ B ∧ gapLength k ≤ H ∧ (Raw k ∨ ¬ EqualEdge (parent k) k) := by
  classical
  simp only [boundedSeeds, Finset.mem_filter, mem_boundedRejections]
  tauto

noncomputable def boundedUnequalParents (B H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range B).filter (fun i ↦ prime (i + 1) ≤ B ∧
    (prime i) ^ 2 ≤ B * gapLength i + prime i * H)

theorem mem_boundedUnequalParents {B H i : ℕ} : i ∈ boundedUnequalParents B H ↔
    prime (i + 1) ≤ B ∧ (prime i) ^ 2 ≤ B * gapLength i + prime i * H := by
  classical
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    have hidx : i + 1 ≤ prime (i + 1) := prime_strictMono.id_le (i + 1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hidx.trans hi.1), hi⟩

theorem boundedRejections_covered (B H : ℕ) :
    boundedRejections B H ⊆ (boundedSeeds B H).biUnion (boundedEqualDescendants B H) := by
  classical
  have hcover : ∀ k, k ∈ boundedRejections B H →
      ∃ i ∈ boundedSeeds B H, k = i ∨ EqualEdge i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      obtain ⟨hRej, hB, hH⟩ := mem_boundedRejections.mp hk
      by_cases hraw : Raw k
      · exact ⟨k, mem_boundedSeeds.mpr ⟨hRej, hB, hH, Or.inl hraw⟩, Or.inl rfl⟩
      by_cases heq : EqualEdge (parent k) k
      · have hlt := parent_lt hRej hraw
        have hpB : prime (parent k + 1) ≤ B :=
          (prime_strictMono.monotone (show parent k + 1 ≤ k + 1 by omega)).trans hB
        have hpmem : parent k ∈ boundedRejections B H :=
          mem_boundedRejections.mpr
            ⟨parent_rejected hRej hraw, hpB, heq.parent_gap_lt.le.trans hH⟩
        obtain ⟨i, hi, hpath⟩ := ih (parent k) hlt hpmem
        refine ⟨i, hi, Or.inr ?_⟩
        rcases hpath with hpi | hpath
        · exact hpi ▸ heq
        · exact hpath.trans heq
      · exact ⟨k, mem_boundedSeeds.mpr ⟨hRej, hB, hH, Or.inr heq⟩, Or.inl rfl⟩
  intro k hk
  obtain ⟨i, hi, hpath⟩ := hcover k hk
  have hmem := mem_boundedRejections.mp hk
  exact Finset.mem_biUnion.mpr
    ⟨i, hi, mem_boundedEqualDescendants.mpr ⟨hmem.2.1, hmem.2.2, hpath⟩⟩

theorem boundedSeeds_covered (B H : ℕ) :
    boundedSeeds B H ⊆ boundedRaw B H ∪
      (boundedUnequalParents B H).biUnion (boundedChildren B H) := by
  classical
  intro k hk
  obtain ⟨hRej, hB, hH, hseed⟩ := mem_boundedSeeds.mp hk
  by_cases hraw : Raw k
  · exact Finset.mem_union_left _ (mem_boundedRaw.mpr ⟨hraw, hB, hH⟩)
  · have hnot := hseed.resolve_left hraw
    have hineq := (parent_bounded_edge_alternatives hRej hraw hB hH).resolve_left hnot
    have hlt := parent_lt hRej hraw
    have hpB : prime (parent k + 1) ≤ B :=
      (prime_strictMono.monotone (show parent k + 1 ≤ k + 1 by omega)).trans hB
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨parent k,
      mem_boundedUnequalParents.mpr ⟨hpB, hineq⟩,
      mem_boundedChildren.mpr ⟨hRej, hraw, hB, hH, rfl⟩⟩)

end Erdos421
