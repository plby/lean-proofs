/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SlowCutoffB4Channels

/-!
# Decomposing a prime common to an integer and its totient
-/

namespace Erdos822

open scoped BigOperators

/-- If a prime divides both `k` and `φ(k)`, it either occurs at least twice
in `k`, or it divides `l-1` for a prime factor `l` of `k`.  This is the
elementary Euler-product decomposition of the internal slow-B4 channel. -/
theorem prime_sq_dvd_or_dvd_primeFactor_pred_of_dvd_totient
    {p k : ℕ} (hp : p.Prime) (hpk : p ∣ k)
    (hpφ : p ∣ Nat.totient k) :
    p ^ 2 ∣ k ∨
      ∃ l ∈ k.primeFactors, p ∣ l - 1 := by
  by_cases hk0 : k = 0
  · subst k
    simp
  rw [Nat.totient_eq_div_primeFactors_mul] at hpφ
  rcases hp.dvd_mul.mp hpφ with hquot | hprod
  · left
    have hpmem : p ∈ k.primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨hp, hpk, hk0⟩
    have hprad : p ∣ ∏ l ∈ k.primeFactors, l :=
      Finset.dvd_prod_of_mem id hpmem
    have hmul :
        (k / ∏ l ∈ k.primeFactors, l) *
            (∏ l ∈ k.primeFactors, l) = k :=
      Nat.div_mul_cancel (Nat.prod_primeFactors_dvd k)
    have hsq : p * p ∣
        (k / ∏ l ∈ k.primeFactors, l) *
          (∏ l ∈ k.primeFactors, l) :=
      mul_dvd_mul hquot hprad
    simpa [pow_two, hmul] using hsq
  · right
    exact hp.prime.dvd_finsetProd_iff
      (fun l : ℕ => l - 1) |>.mp hprod

end Erdos822
