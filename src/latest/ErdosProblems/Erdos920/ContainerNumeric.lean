import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Discrete numerical estimates for the container argument

This file supplies the elementary stopping calculation used with
`Container.PathShrinkCertificate`.  The calculation is deliberately carried
out in `ℕ`: after `2*K` contractions by `(2*K-1)/(2*K)` the potential drops by
at least a factor of two.  Hence a logarithmic number of blocks is enough.
-/

namespace Erdos920.ContainerNumeric

open Finset

/-- A convenient number of halving blocks when the initial potential is at
most `2*q^t`. -/
def stoppingBlocks (t q : ℕ) : ℕ :=
  t * (Nat.log 2 q + 1) + 2

/-- The corresponding number of exceptional steps for a contraction whose
denominator is `2*K`. -/
def contractionBudget (K t q : ℕ) : ℕ :=
  2 * K * stoppingBlocks t q

/-- A deliberately generous coefficient which dominates all exceptional
levels of the projective container. -/
def projectiveBudgetConstant (t : ℕ) : ℕ :=
  320 * t * t * (t + 1)

/-- The two lowest nonzero terms in the binomial expansion already show that
one block of `a+1` contractions halves the potential. -/
theorem two_mul_pow_succ_le_succ_pow (a : ℕ) :
    2 * a ^ (a + 1) ≤ (a + 1) ^ (a + 1) := by
  rw [show a + 1 = a + 1 by rfl, show (a + 1 : ℕ) = a + 1 by rfl,
    add_pow]
  have hs : ({a, a + 1} : Finset ℕ) ⊆ Finset.range (a + 1 + 1) := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp
  calc
    2 * a ^ (a + 1) ≤
        ∑ m ∈ ({a, a + 1} : Finset ℕ),
          a ^ m * 1 ^ (a + 1 - m) * (a + 1).choose m := by
      simp only [one_pow, mul_one, mem_singleton, Nat.left_eq_add, one_ne_zero,
        not_false_eq_true, sum_insert, Nat.choose_succ_self_right, sum_singleton,
        Nat.choose_self]
      rw [Nat.mul_succ]
      rw [pow_succ]
      omega
    _ ≤ ∑ m ∈ Finset.range (a + 1 + 1),
          a ^ m * 1 ^ (a + 1 - m) * (a + 1).choose m := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ ↦ Nat.zero_le _)

/-- Iterating the preceding block estimate. -/
theorem pow_two_mul_pow_pred_le_pow {B r : ℕ} (hB : 1 ≤ B) :
    2 ^ r * (B - 1) ^ (B * r) ≤ B ^ (B * r) := by
  have hblock : 2 * (B - 1) ^ B ≤ B ^ B := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hB
    simpa [Nat.add_sub_cancel_left, Nat.add_comm] using two_mul_pow_succ_le_succ_pow a
  calc
    2 ^ r * (B - 1) ^ (B * r) =
        (2 * (B - 1) ^ B) ^ r := by rw [mul_pow, pow_mul]
    _ ≤ (B ^ B) ^ r := Nat.pow_le_pow_left hblock r
    _ = B ^ (B * r) := by rw [pow_mul]

/-- A number bounded by `2*q^t`, plus one, is below the power of two indexed
by `stoppingBlocks`. -/
theorem initial_lt_two_pow_stoppingBlocks {t q N : ℕ}
    (ht : 1 ≤ t) (_hq : 1 ≤ q) (hN : N ≤ 2 * q ^ t) :
    N + 1 < 2 ^ stoppingBlocks t q := by
  have hqpow : q < 2 ^ (Nat.log 2 q + 1) := by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) q
  have ht0 : t ≠ 0 := by omega
  have hpow : q ^ t < (2 ^ (Nat.log 2 q + 1)) ^ t :=
    Nat.pow_lt_pow_left hqpow ht0
  have hNlt : N < 2 ^ (t * (Nat.log 2 q + 1) + 1) := by
    calc
      N ≤ 2 * q ^ t := hN
      _ < 2 * (2 ^ (Nat.log 2 q + 1)) ^ t :=
        Nat.mul_lt_mul_of_pos_left hpow (by omega)
      _ = 2 ^ (t * (Nat.log 2 q + 1) + 1) := by
        rw [← pow_mul]
        simp [pow_succ', Nat.mul_comm]
  have hsucc : N + 1 ≤ 2 ^ (t * (Nat.log 2 q + 1) + 1) := hNlt
  calc
    N + 1 ≤ 2 ^ (t * (Nat.log 2 q + 1) + 1) := hsucc
    _ < 2 ^ stoppingBlocks t q := by
      unfold stoppingBlocks
      exact Nat.pow_lt_pow_right (by omega) (by omega)

/-- The exact stopping hypothesis expected by
`Container.selectedCount_le_of_certificate`. -/
theorem contraction_stopping {K t q N : ℕ}
    (hK : 1 ≤ K) (ht : 1 ≤ t) (hq : 1 ≤ q) (hN : N ≤ 2 * q ^ t) :
    ∀ c : ℕ, contractionBudget K t q < c →
      (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c := by
  intro c hc
  let B := 2 * K
  let r := stoppingBlocks t q
  have hB : 1 ≤ B := by simp [B]; omega
  have hinit : N + 1 < 2 ^ r := by
    simpa [r] using initial_lt_two_pow_stoppingBlocks ht hq hN
  have hbr : B * r ≤ c := by
    simpa [contractionBudget, B, r] using hc.le
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbr
  have hapos : 0 < (B - 1) ^ (B * r) := pow_pos (by omega) _
  have htailpos : 0 < (B - 1) ^ d := pow_pos (by omega) _
  have htail : (B - 1) ^ d ≤ B ^ d :=
    Nat.pow_le_pow_left (Nat.sub_le B 1) d
  calc
    (2 * K - 1) ^ (B * r + d) * (N + 1) =
        ((B - 1) ^ (B * r) * (N + 1)) * (B - 1) ^ d := by
      simp only [B, pow_add]
      ac_rfl
    _ < ((B - 1) ^ (B * r) * 2 ^ r) * (B - 1) ^ d := by
      exact Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left hinit hapos) htailpos
    _ ≤ B ^ (B * r) * B ^ d := by
      have hblock := pow_two_mul_pow_pred_le_pow (B := B) (r := r) hB
      calc
        ((B - 1) ^ (B * r) * 2 ^ r) * (B - 1) ^ d =
            (2 ^ r * (B - 1) ^ (B * r)) * (B - 1) ^ d := by ac_rfl
        _ ≤ B ^ (B * r) * (B - 1) ^ d := Nat.mul_le_mul_right _ hblock
        _ ≤ B ^ (B * r) * B ^ d := Nat.mul_le_mul_left _ htail
    _ = (2 * K) ^ (B * r + d) := by
      simp only [B, ← pow_add]

/-- Specialization to the cleared-denominator contraction constant in the
projective container. -/
theorem projective_contraction_stopping {t q N : ℕ}
    (ht : 1 ≤ t) (hq : 1 ≤ q) (hN : N ≤ 2 * q ^ t) :
    ∀ c : ℕ, contractionBudget (32 * t * q) t q < c →
      (2 * (32 * t * q) - 1) ^ c * (N + 1) <
        (2 * (32 * t * q)) ^ c := by
  have hK : 1 ≤ 32 * t * q := by
    have : 0 < 32 * t * q := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    omega
  exact contraction_stopping
    (K := 32 * t * q) (t := t) (q := q) (N := N)
    hK ht hq hN

end Erdos920.ContainerNumeric
