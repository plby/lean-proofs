/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.LogFiberMajorant
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Summing the finite beta-sieve remainder

The Rosser remainder in one fiber is the square of a fixed power of the
sieving endpoint.  Choosing that endpoint as a sufficiently deep natural
root of the cofactor scale makes the complete double sum negligible compared
with the ambient sixtieth power.
-/

namespace Erdos822

open scoped BigOperators

/-- The odd raw cofactor layer injects into the initial interval below its
already-proved size bound. -/
theorem oddRawCofactors_card_le_succ_pow_twenty_eight (N : ℕ) :
    (oddRawCofactors N).card ≤ N ^ 28 + 1 := by
  calc
    (oddRawCofactors N).card ≤ (Finset.range (N ^ 28 + 1)).card := by
      apply Finset.card_le_card
      intro m hm
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (oddRawCofactors_le_pow_twenty_eight hm)
    _ = N ^ 28 + 1 := Finset.card_range _

/-- The square beta-sieve remainder at the root cutoff is at most the base
scale itself. -/
theorem slowSieveCutoff_error_sq_le
    (N S : ℕ) (hS : 0 < S) :
    ((Nat.nthRoot (4 * S) N) ^ S) ^ 2 ≤ N := by
  let y := Nat.nthRoot (4 * S) N
  have hroot : y ^ (4 * S) ≤ N := by
    dsimp [y]
    exact (Nat.pow_nthRoot_le_iff).2 (Or.inl (by omega))
  have hpow : (y ^ S) ^ 2 ≤ y ^ (4 * S) := by
    by_cases hy : y = 0
    · rw [hy]
      rw [Nat.zero_pow hS, Nat.zero_pow (by omega : 0 < 4 * S)]
      simp
    · have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy
      calc
        (y ^ S) ^ 2 = y ^ (2 * S) := by
          rw [← pow_mul]
          congr 1
          omega
        _ ≤ y ^ (4 * S) := by
          apply Nat.pow_le_pow_right hy1
          omega
  exact hpow.trans hroot

/-- At the root-scale cutoff every outer prime in the odd raw construction
is safely above the sieving endpoint. -/
theorem oddOuterPrime_gt_slowSieveCutoff
    {N S m p : ℕ} (hN : 2 ≤ N) (hS : 0 < S)
    (hm : m ∈ oddRawCofactors N)
    (hp : p ∈ outerPrimes (N ^ 60) m) :
    Nat.nthRoot (4 * S) N < p := by
  have hroot : Nat.nthRoot (4 * S) N ≤ N :=
    nthRoot_le_self_of_pos (by omega)
  have hNpow : N ≤ N ^ 25 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ N)
      (by omega : 1 ≤ 25)
  calc
    Nat.nthRoot (4 * S) N ≤ N := hroot
    _ ≤ N ^ 25 := hNpow
    _ ≤ m := oddRawCofactors_ge_pow_twenty_five hN hm
    _ < p := oddOuterPrime_large_of_mem hN hm hp

/-- The complete double sum of beta-sieve square remainders over distinct
odd raw cofactors is bounded by a fixed multiple of the ambient scale. -/
theorem sum_oddRaw_slowSieveCutoff_error_sq_le
    (N S : ℕ) (hN : 1 ≤ N) (hS : 0 < S) :
    (∑ m ∈ oddRawCofactors N,
        ∑ m' ∈ (oddRawCofactors N).erase m,
          (((Nat.nthRoot (4 * S) N) ^ S : ℕ) : ℝ) ^ 2) ≤
      4 * ((N ^ 60 : ℕ) : ℝ) := by
  have herrNat :
      ((Nat.nthRoot (4 * S) N) ^ S) ^ 2 ≤ N :=
    slowSieveCutoff_error_sq_le N S hS
  have herr :
      (((Nat.nthRoot (4 * S) N) ^ S : ℕ) : ℝ) ^ 2 ≤
        (N : ℝ) := by
    norm_cast
  have hcardNat :
      (oddRawCofactors N).card ≤ 2 * N ^ 28 := by
    have hbase := oddRawCofactors_card_le_succ_pow_twenty_eight N
    have hpow1 : 1 ≤ N ^ 28 := by
      exact one_le_pow₀ hN
    omega
  have hcard :
      ((oddRawCofactors N).card : ℝ) ≤ (2 * N ^ 28 : ℕ) := by
    exact_mod_cast hcardNat
  calc
    (∑ m ∈ oddRawCofactors N,
        ∑ m' ∈ (oddRawCofactors N).erase m,
          (((Nat.nthRoot (4 * S) N) ^ S : ℕ) : ℝ) ^ 2) ≤
        ∑ m ∈ oddRawCofactors N,
          ∑ m' ∈ (oddRawCofactors N).erase m, (N : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro m' hm'
      exact herr
    _ = ∑ m ∈ oddRawCofactors N,
          (((oddRawCofactors N).erase m).card : ℝ) * N := by
      apply Finset.sum_congr rfl
      intro m hm
      simp
    _ ≤ ∑ m ∈ oddRawCofactors N,
          ((oddRawCofactors N).card : ℝ) * N := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_erase_le (s := oddRawCofactors N) (a := m)
    _ = ((oddRawCofactors N).card : ℝ) ^ 2 * N := by
      simp
      ring
    _ ≤ ((2 * N ^ 28 : ℕ) : ℝ) ^ 2 * N := by
      have h0 : (0 : ℝ) ≤ (oddRawCofactors N).card := by positivity
      have h1 : (0 : ℝ) ≤ (2 * N ^ 28 : ℕ) := by positivity
      have hsquare :
          ((oddRawCofactors N).card : ℝ) ^ 2 ≤
            ((2 * N ^ 28 : ℕ) : ℝ) ^ 2 :=
        (sq_le_sq₀ h0 h1).2 hcard
      exact mul_le_mul_of_nonneg_right hsquare (by positivity)
    _ = 4 * ((N ^ 57 : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ 4 * ((N ^ 60 : ℕ) : ℝ) := by
      have hp : N ^ 57 ≤ N ^ 60 :=
        Nat.pow_le_pow_right hN (by omega : 57 ≤ 60)
      have hpR : ((N ^ 57 : ℕ) : ℝ) ≤ ((N ^ 60 : ℕ) : ℝ) := by
        exact_mod_cast hp
      exact mul_le_mul_of_nonneg_left hpR (by norm_num)

end Erdos822
