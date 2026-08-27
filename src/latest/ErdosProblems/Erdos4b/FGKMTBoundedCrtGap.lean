/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.Base
import Mathlib.NumberTheory.Bertrand

/-! # The CRT gap with a bound on its right-hand prime -/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_bounded_gap_of_composite_block {b y : ℕ} (hb : 2 ≤ b)
    (hcomp : ∀ i : ℕ, 1 ≤ i → i ≤ y → ¬(b + i).Prime) :
    ∃ n : ℕ,
      (y : ℝ) < (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n ∧
      Nat.nth Nat.Prime (n + 1) ≤ 2 * (b + y + 1) := by
  let d := Nat.count Nat.Prime (b + 1)
  have hd : 0 < d := by
    apply Nat.pos_of_ne_zero
    rw [Nat.count_ne_iff_exists]
    exact ⟨2, by omega, Nat.prime_two⟩
  let n := d - 1
  have hn : n + 1 = d := Nat.sub_add_cancel hd
  have hp : Nat.nth Nat.Prime n ≤ b := by
    have hh := Nat.nth_lt_of_lt_count (show n < Nat.count Nat.Prime (b + 1) by omega)
    omega
  have hcount := count_prime_eq_of_composite_block b y hcomp
  have hnext : b + y + 1 ≤ Nat.nth Nat.Prime (n + 1) := by
    have hh := Nat.le_nth_count Nat.infinite_setOfPred_prime (b + y + 1)
    rw [hcount] at hh
    simpa only [hn, d] using hh
  obtain ⟨q, hq, hqgt, hqle⟩ := Nat.exists_prime_lt_and_le_two_mul (b + y + 1) (by omega)
  have hnextle : Nat.nth Nat.Prime (n + 1) ≤ q := by
    rw [hn, ← Nat.nth_count hq]
    apply Nat.nth_monotone Nat.infinite_setOfPred_prime
    exact Nat.count_monotone Nat.Prime (by omega : b + 1 ≤ q)
  refine ⟨n, ?_, hnextle.trans hqle⟩
  have hpR : (Nat.nth Nat.Prime n : ℝ) ≤ b := by exact_mod_cast hp
  have hnextR : (b : ℝ) + y + 1 ≤ Nat.nth Nat.Prime (n + 1) := by exact_mod_cast hnext
  linarith

theorem exists_bounded_gap_of_cover {y q : ℕ} (cover : ResidueCover y)
    (hprime : ∀ p ∈ cover.primes, p ≤ q) :
    ∃ n : ℕ,
      (y : ℝ) < (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n ∧
      Nat.nth Nat.Prime (n + 1) ≤ 2 * (3 * primorial q + y + 1) := by
  have hmod : cover.modulus ≤ primorial q := primeProduct_le_primorial (fun p hp =>
    Nat.mem_primesLE.mpr ⟨hprime p hp, cover.prime p hp⟩)
  obtain ⟨b, hb, hbupper, hcomp⟩ := cover.exists_composite_block_ge 2
  obtain ⟨n, hgap, hright⟩ := exists_bounded_gap_of_composite_block hb hcomp
  refine ⟨n, hgap, hright.trans ?_⟩
  norm_num only [max_eq_left (by norm_num : (1 : ℕ) ≤ 2)] at hbupper
  omega

end

end Erdos4b.FGKMT
