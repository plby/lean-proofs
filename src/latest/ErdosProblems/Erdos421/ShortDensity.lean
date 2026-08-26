import ErdosProblems.Erdos421.ShortGaps
import ErdosProblems.Erdos421.GeometricDensity

/-! # The integers discarded in short gaps have natural density zero -/

namespace Erdos421

def shortOmissions : Set ℕ :=
  {n | ∃ k, Rejected k ∧ ShortGap k ∧ prime k < n ∧ n < prime (k + 1)}

theorem prefixCount_shortOmissions_le {B X : ℕ} (hX : 2 * B ≤ X) :
    prefixCount shortOmissions B ≤ ∑ k ∈ shortRejectedGaps X, gapLength k := by
  classical
  have hsub : (Finset.range B).filter (· ∈ shortOmissions) ⊆
      (shortRejectedGaps X).biUnion (fun k ↦ Finset.Ioo (prime k) (prime (k + 1))) := by
    intro n hn
    obtain ⟨hnB, k, hk, hs, hpn, hnq⟩ := Finset.mem_filter.mp hn
    have hnB' := Finset.mem_range.mp hnB
    have hqX : prime (k + 1) ≤ X := (prime_succ_le_two_mul k).trans
      ((Nat.mul_le_mul_left 2 (show prime k ≤ B by omega)).trans hX)
    exact Finset.mem_biUnion.mpr ⟨k, mem_shortRejectedGaps.mpr ⟨hk, hs, hqX⟩,
      Finset.mem_Ioo.mpr ⟨hpn, hnq⟩⟩
  calc
    prefixCount shortOmissions B ≤
        ((shortRejectedGaps X).biUnion
          (fun k ↦ Finset.Ioo (prime k) (prime (k + 1)))).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ shortRejectedGaps X, (Finset.Ioo (prime k) (prime (k + 1))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ k ∈ shortRejectedGaps X, gapLength k := by
      apply Finset.sum_le_sum
      intro k _
      rw [Nat.card_Ioo]
      unfold gapLength
      omega

theorem shortOmissions_prefix_scale {u : ℕ} (hu : 10 ≤ u) :
    prefixCount shortOmissions (2 ^ (60 * u)) ≤ 18 * 2 ^ (57 * (u + 1)) := by
  apply (prefixCount_shortOmissions_le (X := 2 ^ (60 * (u + 1))) ?_).trans
    (sum_shortRejected_gapLength_scale (by omega))
  calc
    2 * 2 ^ (60 * u) = 2 ^ (60 * u + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (60 * (u + 1)) := Nat.pow_le_pow_right (by decide) (by omega)

/-- This density-zero theorem is unconditional. It covers only the short
rejected gaps, not the still-uncontrolled long prime gaps. -/
theorem shortOmissions_hasDensity_zero : shortOmissions.HasDensity 0 := by
  apply hasDensity_zero_of_geometric_bound shortOmissions
    (a := 2 ^ 57) (b := 2 ^ 60) (C := 18 * 2 ^ 57) (N₀ := 10)
    (by norm_num) (by norm_num)
  intro u hu
  have h := shortOmissions_prefix_scale hu
  have hb : (2 ^ 60) ^ u = 2 ^ (60 * u) := (pow_mul 2 60 u).symm
  have ha : 18 * 2 ^ (57 * (u + 1)) = (18 * 2 ^ 57) * (2 ^ 57) ^ u := by
    rw [Nat.mul_add, Nat.mul_one, pow_add, pow_mul]
    ring
  rwa [hb, ← ha]

/-- All interiors of long prime gaps, whether or not the greedy test rejects them. -/
def longOmissions : Set ℕ :=
  {n | ∃ k, ¬ ShortGap k ∧ prime k < n ∧ n < prime (k + 1)}

theorem candidate_compl_subset :
    candidateᶜ ⊆ Set.Iio 2 ∪ shortOmissions ∪ longOmissions := by
  intro n hn
  by_cases hn2 : n < 2
  · exact Or.inl (Or.inl hn2)
  · obtain ⟨k, hpn, hnq, hk⟩ := omitted_mem_rejected_gap (by omega) hn
    by_cases hs : ShortGap k
    · exact Or.inl (Or.inr ⟨k, hk, hs, hpn, hnq⟩)
    · exact Or.inr ⟨k, hs, hpn, hnq⟩

theorem candidate_compl_prefix_le (N : ℕ) :
    prefixCount candidateᶜ N ≤ 2 + prefixCount shortOmissions N + prefixCount longOmissions N := by
  classical
  have hsub : (Finset.range N).filter (· ∈ candidateᶜ) ⊆
      (Finset.range 2 ∪ (Finset.range N).filter (· ∈ shortOmissions)) ∪
        (Finset.range N).filter (· ∈ longOmissions) := by
    intro n hn
    obtain ⟨hnN, hnot⟩ := Finset.mem_filter.mp hn
    rcases candidate_compl_subset hnot with (hn2 | hs) | hl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr hn2))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnN, hs⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnN, hl⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard' := Finset.card_union_le (Finset.range 2)
    ((Finset.range N).filter (· ∈ shortOmissions))
  simp only [Finset.card_range] at hcard'
  simpa only [prefixCount, Set.mem_compl_iff] using
    hcard.trans (Nat.add_le_add_right hcard' _)

end Erdos421
