import ErdosProblems.Erdos421.BoundedMass
import ErdosProblems.Erdos421.GeometricDensity
import ErdosProblems.Erdos421.LongGaps

/-! # The full complement counted using an absolute gap cutoff -/

namespace Erdos421

noncomputable def largeGapIndices (B H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range B).filter (fun k ↦ prime (k + 1) ≤ B ∧ H < gapLength k)

theorem mem_largeGapIndices {B H k : ℕ} : k ∈ largeGapIndices B H ↔
    prime (k + 1) ≤ B ∧ H < gapLength k := by
  classical
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    have hidx : k + 1 ≤ prime (k + 1) := prime_strictMono.id_le (k + 1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hidx.trans hk.1), hk⟩

theorem candidate_compl_bounded_prefix_le {B X H h : ℕ}
    (hX : 2 * B ≤ X) (hh : 2 * (h + 1) ≤ H) :
    prefixCount candidateᶜ B ≤ 2 +
      (∑ k ∈ boundedRejections X H, gapLength k) + 2 * (primeFreeStarts X h).card := by
  classical
  let S := (boundedRejections X H).biUnion (fun k ↦ Finset.Ioo (prime k) (prime (k + 1)))
  let L := (largeGapIndices X H).biUnion (fun k ↦ Finset.Ioo (prime k) (prime (k + 1)))
  have hsub : (Finset.range B).filter (· ∈ candidateᶜ) ⊆ (Finset.range 2 ∪ S) ∪ L := by
    intro n hn
    obtain ⟨hnB, hn⟩ := Finset.mem_filter.mp hn
    have hnB' := Finset.mem_range.mp hnB
    by_cases hn2 : n < 2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr hn2))
    · obtain ⟨k, hpn, hnq, hk⟩ := omitted_mem_rejected_gap (by omega) hn
      have hqX : prime (k + 1) ≤ X := (prime_succ_le_two_mul k).trans
        ((Nat.mul_le_mul_left 2 (show prime k ≤ B by omega)).trans hX)
      by_cases hg : gapLength k ≤ H
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨k, mem_boundedRejections.mpr ⟨hk, hqX, hg⟩, Finset.mem_Ioo.mpr ⟨hpn, hnq⟩⟩))
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨k, mem_largeGapIndices.mpr ⟨hqX, by omega⟩, Finset.mem_Ioo.mpr ⟨hpn, hnq⟩⟩)
  have hcard (I : Finset ℕ) :
      (I.biUnion (fun k ↦ Finset.Ioo (prime k) (prime (k + 1)))).card ≤
        ∑ k ∈ I, gapLength k := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro k _
    rw [Nat.card_Ioo]
    unfold gapLength
    omega
  have hlarge : (∑ k ∈ largeGapIndices X H, gapLength k) ≤
      2 * (primeFreeStarts X h).card :=
    sum_long_gap_lengths_le _ X h
      (fun k hk ↦ (mem_largeGapIndices.mp hk).1)
      (fun k hk ↦ hh.trans (mem_largeGapIndices.mp hk).2.le)
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := Finset.card_union_le (Finset.range 2) S
  have hS : S.card ≤ ∑ k ∈ boundedRejections X H, gapLength k := hcard _
  have hL : L.card ≤ 2 * (primeFreeStarts X h).card := (hcard _).trans hlarge
  simp only [Finset.card_range] at h2
  have htotal : ((Finset.range B).filter (· ∈ candidateᶜ)).card ≤ 2 +
      (∑ k ∈ boundedRejections X H, gapLength k) + 2 * (primeFreeStarts X h).card := by omega
  simpa only [prefixCount, Set.mem_compl_iff] using htotal

/-- A finite estimate for the entire candidate complement. The exceptional
prime-free-start count on the right is not bounded analytically here. -/
theorem candidate_compl_bounded_prefix_scale {u : ℕ} (hu : 12 ≤ u) :
    prefixCount candidateᶜ (2 ^ (180 * u)) ≤ 2 + 7 * 2 ^ (179 * (u + 1)) +
      2 * (primeFreeStarts (2 ^ (180 * (u + 1))) (2 ^ (19 * u))).card := by
  have hX : 2 * 2 ^ (180 * u) ≤ 2 ^ (180 * (u + 1)) := by
    calc
      _ = 2 ^ (180 * u + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (180 * (u + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  have hh : 2 * (2 ^ (19 * u) + 1) ≤ 2 ^ (19 * (u + 1)) := by
    have hpos : 0 < 2 ^ (19 * u) := by positivity
    calc
      _ ≤ 4 * 2 ^ (19 * u) := by omega
      _ = 2 ^ (19 * u + 2) := by rw [pow_add]; ring
      _ ≤ 2 ^ (19 * (u + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  have h := candidate_compl_bounded_prefix_le hX hh
  have hm := boundedRejections_mass_scale (u := u + 1) (by omega)
  omega

end Erdos421
