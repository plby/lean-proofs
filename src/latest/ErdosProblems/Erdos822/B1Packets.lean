/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B1SecondMoment

/-! # Prime packets and the finite B1 union bound -/

namespace Erdos822

open scoped BigOperators

/-- Primes up to `N` congruent to one modulo `d`, expressed by divisibility
of the predecessor to match the totient product. -/
def b1PrimePacket (N d : ℕ) : Finset ℕ :=
  (Nat.primesLE N).filter fun q ↦ d ∣ q - 1

theorem mem_b1PrimePacket_iff {N d q : ℕ} :
    q ∈ b1PrimePacket N d ↔ q ≤ N ∧ q.Prime ∧ d ∣ q - 1 := by
  simp [b1PrimePacket, Nat.mem_primesLE, and_assoc]

theorem b1PrimePacket_card_le (N d : ℕ) : (b1PrimePacket N d).card ≤ N := by
  calc
    (b1PrimePacket N d).card ≤ (Finset.Icc 1 N).card := by
      apply Finset.card_le_card
      intro q hq
      obtain ⟨hqN, hqp, hqd⟩ := mem_b1PrimePacket_iff.mp hq
      exact Finset.mem_Icc.mpr ⟨hqp.one_le, hqN⟩
    _ = N := by simp

/-- Zero-based sample indices whose positive successor fails B1. -/
noncomputable def b1FailureIndices (N y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun n ↦ ¬ TotientSquareRich (n + 1) y

theorem card_b1FailureIndices_le_sum (N y : ℕ) :
    (b1FailureIndices N y).card ≤
      ∑ d ∈ Finset.Icc 2 y,
        ((Finset.range N).filter
          (fun n ↦ ¬ d ^ 2 ∣ Nat.totient (n + 1))).card := by
  classical
  let F := fun d ↦ (Finset.range N).filter
    (fun n ↦ ¬ d ^ 2 ∣ Nat.totient (n + 1))
  have hsub : b1FailureIndices N y ⊆ (Finset.Icc 2 y).biUnion F := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hfail := hn'.2
    simp only [TotientSquareRich, not_forall] at hfail
    obtain ⟨d, hdpos, hdy, hbad⟩ := hfail
    have hdne : d ≠ 1 := by
      intro hd
      simp [hd] at hbad
    have hd2 : 2 ≤ d := by omega
    exact Finset.mem_biUnion.mpr
      ⟨d, Finset.mem_Icc.mpr ⟨hd2, hdy⟩, Finset.mem_filter.mpr ⟨hn'.1, hbad⟩⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)

/-- The finite B1 exceptional set is small as soon as every packet has
reciprocal mass at least `M / d`.  In the application `M` is a constant
multiple of `log log N`, while `y` is its fourth root. -/
theorem card_b1FailureIndices_mul_le
    (N y : ℕ) {M : ℝ} (hM : 0 ≤ M) (hyM : 2 * (y : ℝ) ≤ M)
    (hpack : ∀ d ∈ Finset.Icc 2 y,
      M ≤ (d : ℝ) * packetPrimeMean (b1PrimePacket N d)) :
    ((b1FailureIndices N y).card : ℝ) * M ≤ 12 * N * (y : ℝ) ^ 2 := by
  classical
  let F := fun d ↦ (Finset.range N).filter
    (fun n ↦ ¬ d ^ 2 ∣ Nat.totient (n + 1))
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 2 y) :
      ((F d).card : ℝ) * M ≤ 12 * N * (d : ℝ) := by
    obtain ⟨hd2, hdy⟩ := Finset.mem_Icc.mp hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hdyR : (d : ℝ) ≤ y := by exact_mod_cast hdy
    have hmean : 2 ≤ packetPrimeMean (b1PrimePacket N d) := by
      apply (mul_le_mul_iff_right₀ hdpos).mp
      have h := hpack d hd
      nlinarith
    have hbound := card_not_sq_dvd_totient_mul_packetMean_le
      N d (b1PrimePacket N d)
      (fun q hq ↦ (mem_b1PrimePacket_iff.mp hq).2.1)
      (b1PrimePacket_card_le N d)
      (fun q hq ↦ (mem_b1PrimePacket_iff.mp hq).2.2) hmean
    calc
      ((F d).card : ℝ) * M ≤
          ((F d).card : ℝ) * ((d : ℝ) * packetPrimeMean (b1PrimePacket N d)) :=
        mul_le_mul_of_nonneg_left (hpack d hd) (by positivity)
      _ = (d : ℝ) * (((F d).card : ℝ) * packetPrimeMean (b1PrimePacket N d)) := by
        ring
      _ ≤ (d : ℝ) * (12 * N) := mul_le_mul_of_nonneg_left hbound hdpos.le
      _ = 12 * N * (d : ℝ) := by ring
  have hsumd : (∑ d ∈ Finset.Icc 2 y, (d : ℝ)) ≤ (y : ℝ) ^ 2 := by
    calc
      (∑ d ∈ Finset.Icc 2 y, (d : ℝ)) ≤ ∑ _d ∈ Finset.Icc 2 y, (y : ℝ) := by
        exact Finset.sum_le_sum fun d hd ↦ by
          exact_mod_cast (Finset.mem_Icc.mp hd).2
      _ = ((Finset.Icc 2 y).card : ℝ) * y := by simp
      _ ≤ (y : ℝ) * y := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (show (Finset.Icc 2 y).card ≤ y by simp)
      _ = (y : ℝ) ^ 2 := by ring
  have hcard : ((b1FailureIndices N y).card : ℝ) ≤
      ∑ d ∈ Finset.Icc 2 y, ((F d).card : ℝ) := by
    exact_mod_cast card_b1FailureIndices_le_sum N y
  calc
    ((b1FailureIndices N y).card : ℝ) * M ≤
        (∑ d ∈ Finset.Icc 2 y, ((F d).card : ℝ)) * M :=
      mul_le_mul_of_nonneg_right hcard hM
    _ = ∑ d ∈ Finset.Icc 2 y, ((F d).card : ℝ) * M := by rw [Finset.sum_mul]
    _ ≤ ∑ d ∈ Finset.Icc 2 y, 12 * N * (d : ℝ) := Finset.sum_le_sum hterm
    _ = 12 * N * ∑ d ∈ Finset.Icc 2 y, (d : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 12 * N * (y : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsumd (by positivity)

end Erdos822
