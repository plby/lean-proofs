import Util.Bernays.LocalLogConvolution

/-!
# Reducing the logarithmic kernel to primes

Higher prime powers contribute at most twice `ψ(N)-θ(N)`. Thus the linear
asymptotic for the full kernel is reduced to the first-prime-power term.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

noncomputable def localAllowedPrimeLog (S : ℕ → Prop) (N : ℕ) : ℝ :=
  ∑ p ∈ (N + 1).primesBelow, if S p then 0 else log p

theorem localLogCoeff_one (S : ℕ → Prop) (p : ℕ) :
    localLogCoeff S p 1 = if S p then 0 else log p := by
  simp [localLogCoeff]

theorem localLogCoeff_le_two_log (S : ℕ → Prop) (p k : ℕ) :
    localLogCoeff S p k ≤ 2 * log p := by
  have hp := log_natCast_nonneg p
  unfold localLogCoeff
  split_ifs <;> linarith

theorem localLogCoeff_sum_bounds (S : ℕ → Prop) {p : ℕ} (hp : p.Prime)
    {K : ℕ} (hK : 1 ≤ K) :
    (if S p then 0 else log p) ≤ ∑ k ∈ Finset.Icc 1 K, localLogCoeff S p k ∧
      (∑ k ∈ Finset.Icc 1 K, localLogCoeff S p k) ≤
        (if S p then 0 else log p) + 2 * ((K : ℝ) * log p - log p) := by
  have hmem : 1 ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_rfl, hK⟩
  constructor
  · rw [← localLogCoeff_one S p]
    exact Finset.single_le_sum (fun k _ => localLogCoeff_nonneg S k hp) hmem
  · have hrest : (∑ k ∈ (Finset.Icc 1 K).erase 1, localLogCoeff S p k) ≤
        2 * ((K : ℝ) * log p - log p) := by
      calc
        _ ≤ ∑ _k ∈ (Finset.Icc 1 K).erase 1, 2 * log p :=
          Finset.sum_le_sum (fun k _ => localLogCoeff_le_two_log S p k)
        _ = 2 * ((K : ℝ) * log p - log p) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hmem]
          simp only [Nat.card_Icc, Nat.add_sub_cancel]
          rw [Nat.cast_sub hK, Nat.cast_one]
          ring
    have hsum := Finset.sum_erase_add (Finset.Icc 1 K) (localLogCoeff S p) hmem
    rw [localLogCoeff_one S p] at hsum
    linarith

theorem localLogMass_prime_bounds (S : ℕ → Prop) (N : ℕ) :
    localAllowedPrimeLog S N ≤ localLogMass S N ∧
      localLogMass S N ≤ localAllowedPrimeLog S N +
        2 * (Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ)) := by
  have hpoint (p : ℕ) (hp : p ∈ (N + 1).primesBelow) :=
    localLogCoeff_sum_bounds S (Nat.prime_of_mem_primesBelow hp)
      (Nat.le_log_of_pow_le (Nat.prime_of_mem_primesBelow hp).one_lt
        (by have := (Nat.mem_primesBelow.mp hp).1; simpa using (show p ≤ N by omega)))
  constructor
  · apply Finset.sum_le_sum
    intro p hp
    exact (hpoint p hp).1
  · calc
      localLogMass S N ≤ ∑ p ∈ (N + 1).primesBelow,
          ((if S p then 0 else log p) + 2 * ((Nat.log p N : ℝ) * log p - log p)) :=
        Finset.sum_le_sum fun p hp => (hpoint p hp).2
      _ = _ := by
        rw [Chebyshev.psi_eq_sum_mul_log_prime, Chebyshev.theta_eq_sum_primesLE_log]
        simp only [Nat.primesLE, localAllowedPrimeLog, Finset.sum_add_distrib]
        congr 1
        rw [← Finset.sum_sub_distrib]
        exact (Finset.mul_sum _ _ _).symm

end Bernays
