import ErdosProblems.Erdos421.PrimeFreeDyadicStarts
import Mathlib.Tactic

/-! # Summing dyadic exceptional-start bounds to a full prefix -/

namespace Erdos421

theorem primeFreeStarts_dyadic_prefix_bound {K N H : ℕ} (hKN : K ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (hlocal : ∀ k : ℕ, K ≤ k → k < N →
      ((primeFreeDyadicStarts (2 ^ k) H).card : ℝ) ≤ ε * (2 : ℝ) ^ k) :
    ((primeFreeStarts (2 ^ N) H).card : ℝ) ≤ (2 : ℝ) ^ K + ε * (2 : ℝ) ^ N := by
  revert hlocal
  induction N, hKN using Nat.le_induction with
  | base =>
    intro hlocal
    have h : ((primeFreeStarts (2 ^ K) H).card : ℝ) ≤ (2 : ℝ) ^ K :=
      by exact_mod_cast primeFreeStarts_card_le (2 ^ K) H
    exact h.trans (le_add_of_nonneg_right (by positivity))
  | succ N hKN ih =>
    intro hlocal
    have hprev := ih (fun k hKk hk ↦ hlocal k hKk (by omega))
    have hnext := hlocal N hKN (Nat.lt_succ_self N)
    have hrec := primeFreeStarts_double_card (2 ^ N) H
    have hpow : 2 * 2 ^ N = 2 ^ (N + 1) := by rw [pow_succ]; ring
    rw [hpow] at hrec
    have hrecR : ((primeFreeStarts (2 ^ (N + 1)) H).card : ℝ) =
        (primeFreeStarts (2 ^ N) H).card + (primeFreeDyadicStarts (2 ^ N) H).card :=
      by exact_mod_cast hrec
    rw [hrecR]
    exact (add_le_add hprev hnext).trans_eq (by rw [pow_succ]; ring)

end Erdos421
