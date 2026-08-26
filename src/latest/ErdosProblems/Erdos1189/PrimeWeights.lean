/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Complete subset sums of the weights p-1 for consecutive primes.
Informal source: Lemma 6.1 of Pickhardt and Omniscience Research Agent,
"Irreducible Covering Sets: A Solution of Erdős Problem 1189".
Formal author: OpenAI Codex.
-/

import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Erdos1189

open Finset

noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime n

lemma primeAt_prime (n : ℕ) : (primeAt n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n

lemma primeAt_strictMono : StrictMono primeAt :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

lemma primeAt_zero : primeAt 0 = 2 := Nat.nth_prime_zero_eq_two

lemma primeAt_succ_lt_two_mul (n : ℕ) : primeAt (n + 1) < 2 * primeAt n := by
  obtain ⟨q, hq, hpq, hqp⟩ := Nat.exists_prime_lt_and_le_two_mul (primeAt n)
    (primeAt_prime n).ne_zero
  have hnext : primeAt (n + 1) ≤ q := by
    by_contra hn
    have hle := Nat.le_nth_of_lt_nth_succ (p := Nat.Prime) (by simpa [primeAt] using
      (lt_of_not_ge hn)) hq
    exact (not_le_of_gt hpq) hle
  have hne : q ≠ 2 * primeAt n := by
    intro heq
    rw [heq] at hq
    exact Nat.not_prime_mul (by decide) (primeAt_prime n).ne_one hq
  exact hnext.trans_lt (lt_of_le_of_ne hqp hne)

noncomputable def primeWeightPrefix (s : ℕ) : ℕ :=
  ∑ i ∈ range s, (primeAt i - 1)

lemma primeWeightPrefix_succ (s : ℕ) :
    primeWeightPrefix (s + 1) = primeWeightPrefix s + (primeAt s - 1) :=
  sum_range_succ _ _

lemma primeAt_le_prefix_add_two (s : ℕ) : primeAt s ≤ primeWeightPrefix s + 2 := by
  induction s with
  | zero => simp [primeAt_zero, primeWeightPrefix]
  | succ s ih =>
      have hp := (primeAt_prime s).two_le
      have hn := primeAt_succ_lt_two_mul s
      rw [primeWeightPrefix_succ]
      omega

lemma prime_weight_le_prefix_add_one (s : ℕ) : primeAt s - 1 ≤ primeWeightPrefix s + 1 := by
  have := primeAt_le_prefix_add_two s
  omega

lemma primeAt_sub_one_le_two_pow (s : ℕ) : primeAt s - 1 ≤ 2 ^ s := by
  induction s with
  | zero => simp [primeAt_zero]
  | succ s ih =>
      have hp := (primeAt_prime s).two_le
      have hn := primeAt_succ_lt_two_mul s
      rw [pow_succ]
      omega

/-- Every integer up to the sum of the first `s` prime weights is a subset sum. -/
theorem prime_weights_complete (s : ℕ) {δ : ℕ} (hδ : δ ≤ primeWeightPrefix s) :
    ∃ T ⊆ range s, (∑ i ∈ T, (primeAt i - 1)) = δ := by
  induction s generalizing δ with
  | zero =>
      have hd : δ = 0 := by simpa [primeWeightPrefix] using hδ
      exact ⟨∅, by simp, by simp [hd]⟩
  | succ s ih =>
      by_cases hd : δ ≤ primeWeightPrefix s
      · obtain ⟨T, hT, hsum⟩ := ih hd
        exact ⟨T, hT.trans (range_mono (Nat.le_succ s)), hsum⟩
      · have hw := prime_weight_le_prefix_add_one s
        have hsum := primeWeightPrefix_succ s
        have hδw : primeAt s - 1 ≤ δ := by omega
        have hrem : δ - (primeAt s - 1) ≤ primeWeightPrefix s := by omega
        obtain ⟨T, hT, hTsum⟩ := ih hrem
        have hs : s ∉ T := fun h => (Nat.lt_irrefl s) (mem_range.mp (hT h))
        refine ⟨insert s T, ?_, ?_⟩
        · exact insert_subset (mem_range.mpr (Nat.lt_succ_self s))
            (hT.trans (range_mono (Nat.le_succ s)))
        · rw [sum_insert hs, hTsum]
          omega

lemma primeAt_le_iff {i B : ℕ} : primeAt i ≤ B ↔ i < Nat.primeCounting B := by
  simpa only [primeAt, Nat.primeCounting, Nat.primeCounting', Nat.lt_succ_iff] using
    (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime (a := i) (b := B + 1)).symm

lemma image_primeAt_range (B : ℕ) :
    (range (Nat.primeCounting B)).image primeAt = Nat.primesLE B := by
  ext p
  simp only [mem_image, mem_range, Nat.mem_primesLE]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨primeAt_le_iff.mpr hi, primeAt_prime i⟩
  · rintro ⟨hpB, hp⟩
    obtain ⟨i, _, hi⟩ := Nat.exists_lt_card_nth_eq hp
    have hi' : primeAt i = p := hi
    exact ⟨i, primeAt_le_iff.mp (hi' ▸ hpB), hi'⟩

def primeWeightSum (B : ℕ) : ℕ := ∑ p ∈ Nat.primesLE B, (p - 1)

lemma primeWeightSum_eq_prefix (B : ℕ) :
    primeWeightSum B = primeWeightPrefix (Nat.primeCounting B) := by
  rw [primeWeightSum, ← image_primeAt_range, sum_image
    (fun _ _ _ _ heq => primeAt_strictMono.injective heq)]
  rfl

/-- The cutoff version of the complete prime-weight subset-sum theorem. -/
theorem prime_weights_complete_cutoff (B : ℕ) {δ : ℕ} (hδ : δ ≤ primeWeightSum B) :
    ∃ D ⊆ Nat.primesLE B, (∑ p ∈ D, (p - 1)) = δ := by
  rw [primeWeightSum_eq_prefix] at hδ
  obtain ⟨T, hT, hsum⟩ := prime_weights_complete (Nat.primeCounting B) hδ
  refine ⟨T.image primeAt, ?_, ?_⟩
  · rw [← image_primeAt_range]
    exact image_subset_image hT
  · rw [sum_image (fun _ _ _ _ heq => primeAt_strictMono.injective heq)]
    exact hsum

end Erdos1189
