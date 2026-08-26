import ErdosProblems.Erdos421.SequenceBlocks

/-! # Witness length bounds independent of the chosen short-gap threshold -/

namespace Erdos421

theorem RawWitness.laterLength_le_gap {k : ℕ} (w : RawWitness k) :
    w.laterLength ≤ gapLength k := by
  unfold RawWitness.laterLength gapLength
  have := w.gap_left
  have := w.gap_right
  have := w.later_nonempty
  omega

theorem RejectedWitness.laterLength_le_gap {k : ℕ} (w : RejectedWitness k) :
    w.n - w.m + 1 ≤ gapLength k := by
  unfold gapLength
  have := w.gap_left
  have := w.gap_right
  have := w.later_nonempty
  omega

theorem RawWitness.length_le_log_mul_later {k K : ℕ} (w : RawWitness k)
    (hB : prime (k + 1) ≤ 2 ^ K) : w.earlierLength ≤ K * w.laterLength := by
  have hpower := witness_power_bound
    (by intro e he; have := (Finset.mem_Icc.mp he).1; have := w.two_le_a; omega)
    (by
      intro t ht
      exact ((Finset.mem_Icc.mp ht).2.trans w.gap_right.le).trans hB) w.product_eq
  rw [w.earlier_card, w.later_card, ← pow_mul] at hpower
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpower

theorem RawWitness.length_le_log_mul_gap {k K : ℕ} (w : RawWitness k)
    (hB : prime (k + 1) ≤ 2 ^ K) : w.earlierLength ≤ K * gapLength k :=
  (w.length_le_log_mul_later hB).trans (Nat.mul_le_mul_left K w.laterLength_le_gap)

theorem RejectedWitness.length_le_log_mul_later {k K : ℕ} (w : RejectedWitness k)
    (hB : prime (k + 1) ≤ 2 ^ K) : w.E.card ≤ K * (w.n - w.m + 1) := by
  have htwo : ∀ e ∈ w.E, 2 ≤ e := by
    intro e he
    rcases Finset.mem_union.mp (w.earlier_block.subset he) with h | h
    · exact (stage_bounds k e h).1
    · exact (prime_prime k).two_le.trans (Finset.mem_Ioc.mp h).1.le
  have hpower := witness_power_bound htwo
    (by
      intro t ht
      exact ((Finset.mem_Icc.mp ht).2.trans w.gap_right.le).trans hB) w.product_eq
  rw [w.later_card, ← pow_mul] at hpower
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpower

theorem RejectedWitness.length_le_log_mul_gap {k K : ℕ} (w : RejectedWitness k)
    (hB : prime (k + 1) ≤ 2 ^ K) : w.E.card ≤ K * gapLength k :=
  (w.length_le_log_mul_later hB).trans (Nat.mul_le_mul_left K w.laterLength_le_gap)

end Erdos421
