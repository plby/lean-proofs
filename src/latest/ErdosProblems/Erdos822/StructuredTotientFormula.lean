/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.Core

/-!
# Elementary totient formulas for structured cofactors

This lightweight file isolates the two multiplicative identities shared by
the slow-cutoff deletion and the determinant argument.
-/

namespace Erdos822

/-- Additive form of the shifted-totient identity. -/
theorem shiftedTotient_mul_prime_add_totient_basic
    {l q : ℕ} (hq : q.Prime) (hql : ¬ q ∣ l) :
    shiftedTotient (l * q) + Nat.totient l =
      shiftedTotient l * q := by
  rw [shiftedTotient_mul_prime hq hql]
  apply Nat.sub_add_cancel
  calc
    Nat.totient l ≤ shiftedTotient l := by
      simpa [shiftedTotient] using Nat.le_add_left l (Nat.totient l)
    _ = shiftedTotient l * 1 := by simp
    _ ≤ shiftedTotient l * q :=
      Nat.mul_le_mul_left _ hq.one_le

/-- Totient factorization for one small factor and two successive new
prime factors. -/
theorem totient_mul_two_primes
    {k r q : ℕ} (hr : r.Prime) (hq : q.Prime)
    (hrk : ¬ r ∣ k) (hqkr : ¬ q ∣ k * r) :
    Nat.totient (k * r * q) =
      Nat.totient k * (r - 1) * (q - 1) := by
  calc
    Nat.totient (k * r * q) =
        Nat.totient (q * (k * r)) := by
      congr 1
      ring
    _ = (q - 1) * Nat.totient (k * r) := by
      rw [Nat.totient_mul_of_prime_of_not_dvd hq hqkr]
    _ = (q - 1) * ((r - 1) * Nat.totient k) := by
      rw [show k * r = r * k by ring,
        Nat.totient_mul_of_prime_of_not_dvd hr hrk]
    _ = Nat.totient k * (r - 1) * (q - 1) := by ring

end Erdos822
