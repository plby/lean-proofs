import ErdosProblems.Erdos421.ChildCount
import ErdosProblems.Erdos421.EqualDescendants
import ErdosProblems.Erdos421.UnequalParentCount

/-!
# A sufficient bound for all short rejected gaps

This proof uses a coarser direct count of unequal parents. The resulting
exponent suffices for the original density assertion; no prime-distribution
estimate is used in this file.
-/

namespace Erdos421

noncomputable def shortRejectedGaps (B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range B).filter (fun k ↦ Rejected k ∧ ShortGap k ∧ prime (k + 1) ≤ B)

theorem mem_shortRejectedGaps {B k : ℕ} : k ∈ shortRejectedGaps B ↔
    Rejected k ∧ ShortGap k ∧ prime (k + 1) ≤ B := by
  classical
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    have hidx : k + 1 ≤ prime (k + 1) := prime_strictMono.id_le (k + 1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hidx.trans hk.2.2), hk⟩

noncomputable def shortSeeds (B : ℕ) : Finset ℕ := by
  classical
  exact (shortRejectedGaps B).filter (fun k ↦ Raw k ∨ ¬ EqualEdge (parent k) k)

theorem mem_shortSeeds {B k : ℕ} : k ∈ shortSeeds B ↔
    Rejected k ∧ ShortGap k ∧ prime (k + 1) ≤ B ∧ (Raw k ∨ ¬ EqualEdge (parent k) k) := by
  classical
  simp only [shortSeeds, Finset.mem_filter, mem_shortRejectedGaps]
  tauto

theorem shortRejectedGaps_covered (B : ℕ) :
    shortRejectedGaps B ⊆ (shortSeeds B).biUnion (equalDescendants B) := by
  classical
  intro k hk
  have hcover : ∀ k, k ∈ shortRejectedGaps B →
      ∃ i ∈ shortSeeds B, k = i ∨ EqualEdge i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      obtain ⟨hRej, hshort, hB⟩ := mem_shortRejectedGaps.mp hk
      by_cases hraw : Raw k
      · exact ⟨k, mem_shortSeeds.mpr ⟨hRej, hshort, hB, Or.inl hraw⟩, Or.inl rfl⟩
      by_cases heq : EqualEdge (parent k) k
      · have hlt := parent_lt hRej hraw
        have hpB : prime (parent k + 1) ≤ B :=
          (prime_strictMono.monotone (show parent k + 1 ≤ k + 1 by omega)).trans hB
        have hpmem : parent k ∈ shortRejectedGaps B :=
          mem_shortRejectedGaps.mpr ⟨parent_rejected hRej hraw, heq.short_parent hshort, hpB⟩
        obtain ⟨i, hi, hpath⟩ := ih (parent k) hlt hpmem
        refine ⟨i, hi, Or.inr ?_⟩
        rcases hpath with hpi | hpath
        · exact hpi ▸ heq
        · exact hpath.trans heq
      · exact ⟨k, mem_shortSeeds.mpr ⟨hRej, hshort, hB, Or.inr heq⟩, Or.inl rfl⟩
  obtain ⟨i, hi, hpath⟩ := hcover k hk
  have hmem := mem_shortRejectedGaps.mp hk
  exact Finset.mem_biUnion.mpr ⟨i, hi, mem_equalDescendants.mpr ⟨hmem.2.1, hmem.2.2, hpath⟩⟩

noncomputable def possibleUnequalParents (u : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 ^ (60 * u))).filter (fun i ↦
    prime (i + 1) ≤ 2 ^ (60 * u) ∧ (prime i) ^ 2 ≤
      2 ^ (60 * u) * gapLength i + prime i * 2 ^ (3 * u))

theorem mem_possibleUnequalParents {u i : ℕ} : i ∈ possibleUnequalParents u ↔
    prime (i + 1) ≤ 2 ^ (60 * u) ∧ (prime i) ^ 2 ≤
      2 ^ (60 * u) * gapLength i + prime i * 2 ^ (3 * u) := by
  classical
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    have hidx : i + 1 ≤ prime (i + 1) := prime_strictMono.id_le (i + 1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hidx.trans hi.1), hi⟩

theorem possibleUnequalParents_card {u : ℕ} (hu : 1 ≤ u) :
    (possibleUnequalParents u).card ≤ 3 * 2 ^ (40 * u) :=
  unequal_parent_card_bound _ hu
    (fun _ hi ↦ (mem_possibleUnequalParents.mp hi).1)
    (fun _ hi ↦ (mem_possibleUnequalParents.mp hi).2)

theorem shortSeeds_covered (u : ℕ) :
    shortSeeds (2 ^ (60 * u)) ⊆ shortRawGaps (2 ^ (60 * u)) ∪
      (possibleUnequalParents u).biUnion (shortChildren (2 ^ (60 * u))) := by
  classical
  intro k hk
  obtain ⟨hRej, hshort, hB, hseed⟩ := mem_shortSeeds.mp hk
  by_cases hraw : Raw k
  · exact Finset.mem_union_left _ (mem_shortRawGaps.mpr ⟨hraw, hshort, hB⟩)
  · have hnot := hseed.resolve_left hraw
    have hineq := (parent_edge_alternatives hRej hraw hshort hB).resolve_left hnot
    have hlt := parent_lt hRej hraw
    have hpB : prime (parent k + 1) ≤ 2 ^ (60 * u) :=
      (prime_strictMono.monotone (show parent k + 1 ≤ k + 1 by omega)).trans hB
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨parent k,
      mem_possibleUnequalParents.mpr ⟨hpB, hineq⟩,
      mem_shortChildren.mpr ⟨hRej, hraw, hshort, hB, rfl⟩⟩)

theorem shortSeeds_card_scale {u : ℕ} (hu : 10 ≤ u) :
    (shortSeeds (2 ^ (60 * u))).card ≤ 9 * 2 ^ (51 * u) := by
  classical
  have hchildren : ((possibleUnequalParents u).biUnion
      (shortChildren (2 ^ (60 * u)))).card ≤ 3 * 2 ^ (51 * u) := by
    calc
      _ ≤ (possibleUnequalParents u).card * 2 ^ (11 * u) :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun i _ ↦ shortChildren_card_scale i hu)
      _ ≤ (3 * 2 ^ (40 * u)) * 2 ^ (11 * u) :=
        Nat.mul_le_mul_right _ (possibleUnequalParents_card (by omega))
      _ = 3 * 2 ^ (51 * u) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega
  have hraw : (shortRawGaps (2 ^ (60 * u))).card ≤ 6 * 2 ^ (51 * u) :=
    (shortRawGaps_card_scale hu).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hcard := (Finset.card_le_card (shortSeeds_covered u)).trans (Finset.card_union_le _ _)
  omega

/-- A coarse exponent `9/10` for the number of short rejected gaps. -/
theorem shortRejectedGaps_card_scale {u : ℕ} (hu : 10 ≤ u) :
    (shortRejectedGaps (2 ^ (60 * u))).card ≤ 18 * 2 ^ (54 * u) := by
  classical
  have hdesc : ∀ i, (equalDescendants (2 ^ (60 * u)) i).card ≤ 2 * 2 ^ (3 * u) := by
    intro i
    have h := equalDescendants_card_scale i u
    have hpos : 0 < 2 ^ (3 * u) := by positivity
    omega
  calc
    _ ≤ ((shortSeeds (2 ^ (60 * u))).biUnion (equalDescendants (2 ^ (60 * u)))).card :=
      Finset.card_le_card (shortRejectedGaps_covered _)
    _ ≤ (shortSeeds (2 ^ (60 * u))).card * (2 * 2 ^ (3 * u)) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun i _ ↦ hdesc i)
    _ ≤ (9 * 2 ^ (51 * u)) * (2 * 2 ^ (3 * u)) :=
      Nat.mul_le_mul_right _ (shortSeeds_card_scale hu)
    _ = 18 * 2 ^ (54 * u) := by
      calc
        _ = 18 * (2 ^ (51 * u) * 2 ^ (3 * u)) := by ring
        _ = _ := by rw [← pow_add]; congr 2; omega

/-- Short rejected gaps discard at most `18 X^(19/20)` integers at this scale. -/
theorem sum_shortRejected_gapLength_scale {u : ℕ} (hu : 10 ≤ u) :
    (∑ k ∈ shortRejectedGaps (2 ^ (60 * u)), gapLength k) ≤ 18 * 2 ^ (57 * u) := by
  calc
    _ ≤ (shortRejectedGaps (2 ^ (60 * u))).card * 2 ^ (3 * u) := by
      apply Finset.sum_le_card_nsmul
      intro k hk
      have h := mem_shortRejectedGaps.mp hk
      exact h.2.1.length_le_scale h.2.2
    _ ≤ (18 * 2 ^ (54 * u)) * 2 ^ (3 * u) :=
      Nat.mul_le_mul_right _ (shortRejectedGaps_card_scale hu)
    _ = 18 * 2 ^ (57 * u) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega

end Erdos421
