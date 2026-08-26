import ErdosProblems.Erdos421.ShortDensity
import ErdosProblems.Erdos421.LongGaps

/-! # A direct finite bound on long-gap omissions -/

namespace Erdos421

noncomputable def longGapsAbove (Y B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * B)).filter
    (fun k ↦ Y ≤ prime k ∧ prime k < B ∧ ¬ ShortGap k)

theorem mem_longGapsAbove {Y B k : ℕ} : k ∈ longGapsAbove Y B ↔
    Y ≤ prime k ∧ prime k < B ∧ ¬ ShortGap k := by
  classical
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    have hidx : k ≤ prime k := prime_strictMono.id_le k
    have hkB : k < B := hidx.trans_lt hk.2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk⟩

theorem long_gap_length_lower {k Y H : ℕ} (hY : Y ≤ prime k)
    (hH : (2 * (H + 1)) ^ 20 ≤ Y) (hlong : ¬ ShortGap k) :
    2 * (H + 1) ≤ gapLength k := by
  by_contra h
  have hgap : gapLength k ≤ 2 * (H + 1) := by omega
  exact hlong ((Nat.pow_le_pow_left hgap 20).trans (hH.trans hY))

theorem prefixCount_longOmissions_le (Y B : ℕ) :
    prefixCount longOmissions B ≤ 2 * Y + ∑ k ∈ longGapsAbove Y B, gapLength k := by
  classical
  let U := (longGapsAbove Y B).biUnion (fun k ↦ Finset.Ioo (prime k) (prime (k + 1)))
  have hsub : (Finset.range B).filter (· ∈ longOmissions) ⊆ Finset.range (2 * Y) ∪ U := by
    intro n hn
    obtain ⟨hnB, k, hlong, hpn, hnq⟩ := Finset.mem_filter.mp hn
    have hnB' := Finset.mem_range.mp hnB
    by_cases hpY : prime k < Y
    · have hq := prime_succ_le_two_mul k
      exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨k, mem_longGapsAbove.mpr ⟨by omega, by omega, hlong⟩,
          Finset.mem_Ioo.mpr ⟨hpn, hnq⟩⟩)
  have hU : U.card ≤ ∑ k ∈ longGapsAbove Y B, gapLength k := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro k _
    rw [Nat.card_Ioo]
    unfold gapLength
    omega
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_range] at hcard
  exact hcard.trans (Nat.add_le_add_left hU _)

/-- The entire long-gap prefix is charged to a small initial segment and
prime-free starts of one fixed interval length. No distribution estimate is assumed. -/
theorem prefixCount_longOmissions_le_primeFree (Y B H : ℕ)
    (hH : (2 * (H + 1)) ^ 20 ≤ Y) :
    prefixCount longOmissions B ≤ 2 * Y + 2 * (primeFreeStarts (2 * B) H).card := by
  apply (prefixCount_longOmissions_le Y B).trans
  apply Nat.add_le_add_left
  apply sum_long_gap_lengths_le (longGapsAbove Y B) (2 * B) H
  · intro k hk
    have h := mem_longGapsAbove.mp hk
    exact (prime_succ_le_two_mul k).trans (Nat.mul_le_mul_left 2 h.2.1.le)
  · intro k hk
    have h := mem_longGapsAbove.mp hk
    exact long_gap_length_lower h.1 hH h.2.2

theorem longOmissions_prefix_scale {u : ℕ} (hu : 4 ≤ u) :
    prefixCount longOmissions (2 ^ (420 * u)) ≤ 2 * 2 ^ (410 * u) +
      2 * (primeFreeStarts (2 ^ (420 * u + 1)) (2 ^ (20 * u))).card := by
  have hH : (2 * (2 ^ (20 * u) + 1)) ^ 20 ≤ 2 ^ (410 * u) := by
    have hpos : 0 < 2 ^ (20 * u) := by positivity
    have hbase : 2 * (2 ^ (20 * u) + 1) ≤ 2 ^ (20 * u + 2) := by
      rw [pow_add]
      norm_num
      omega
    calc
      _ ≤ (2 ^ (20 * u + 2)) ^ 20 := Nat.pow_le_pow_left hbase 20
      _ = 2 ^ ((20 * u + 2) * 20) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ (410 * u) := Nat.pow_le_pow_right (by decide) (by omega)
  have h := prefixCount_longOmissions_le_primeFree
    (2 ^ (410 * u)) (2 ^ (420 * u)) (2 ^ (20 * u)) hH
  have hpow : 2 * 2 ^ (420 * u) = 2 ^ (420 * u + 1) := by rw [pow_succ]; ring
  rwa [hpow] at h

end Erdos421
