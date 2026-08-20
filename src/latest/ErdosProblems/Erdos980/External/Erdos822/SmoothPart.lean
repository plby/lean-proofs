/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.Core

/-!
# Smooth parts for Erdős Problem 822

The GIL proof partitions cofactors by the divisor supported on primes at
most `y`.  This file supplies the exact arithmetic object and its elementary
factorization facts; the later normal-order estimate is a separate analytic
theorem.
-/

namespace Erdos822

/-- The part of `n.factorization` supported on primes at most `y`. -/
def smoothFactorization (n y : ℕ) : ℕ →₀ ℕ :=
  n.factorization.filter fun p ↦ p ≤ y

/-- `D(n,y)`, the factor of `n` supported on primes at most `y`. -/
def smoothPart (n y : ℕ) : ℕ :=
  (smoothFactorization n y).prod fun p e ↦ p ^ e

lemma smoothFactorization_le_factorization (n y : ℕ) :
    smoothFactorization n y ≤ n.factorization := by
  intro p
  simp only [smoothFactorization, Finsupp.filter_apply]
  split <;> simp

/-- Taking the factorization of the smooth part recovers the filtered
factorization. -/
lemma factorization_smoothPart (n y : ℕ) :
    (smoothPart n y).factorization = smoothFactorization n y := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (smoothFactorization_le_factorization n y)

/-- The smooth part is a divisor of the original integer. -/
lemma smoothPart_dvd (n y : ℕ) : smoothPart n y ∣ n := by
  exact Nat.prod_pow_dvd_of_le_factorization
    (smoothFactorization_le_factorization n y)

/-- A prime occurs in the smooth part exactly when it occurs in `n` and is
at most the cutoff. -/
lemma mem_primeFactors_smoothPart_iff {n y p : ℕ} :
    p ∈ (smoothPart n y).primeFactors ↔ p ∈ n.primeFactors ∧ p ≤ y := by
  change p ∈ (smoothPart n y).factorization.support ↔
    p ∈ n.factorization.support ∧ p ≤ y
  rw [factorization_smoothPart]
  simp [smoothFactorization, Finsupp.support_filter]

/-- For a positive integer, the smooth part is bounded by the integer. -/
lemma smoothPart_le {n y : ℕ} (hn : 0 < n) : smoothPart n y ≤ n := by
  exact Nat.le_of_dvd hn (smoothPart_dvd n y)

/-- The precise smooth-part preservation conclusion used to place two
colliding cofactors in the same `B_d`: sufficiently many small prime powers
in `φ(m)` make the smooth part of `m + φ(m)` equal that of `m`. -/
lemma smoothFactorization_shiftedTotient_eq {m y : ℕ} (hm : 0 < m)
    (hφ : ∀ p : ℕ, p.Prime → p ≤ y →
      ∀ a : ℕ, a ≤ m.factorization p + 1 → p ^ a ∣ Nat.totient m) :
    smoothFactorization (shiftedTotient m) y = smoothFactorization m y := by
  ext p
  simp only [smoothFactorization, Finsupp.filter_apply]
  by_cases hpy : p ≤ y
  · simp only [hpy, ↓reduceIte]
    by_cases hp : p.Prime
    · exact factorization_shiftedTotient_eq_of_pow_dvd_totient hp hm
        (hφ p hp hpy)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  · simp [hpy]

lemma smoothPart_shiftedTotient_eq {m y : ℕ} (hm : 0 < m)
    (hφ : ∀ p : ℕ, p.Prime → p ≤ y →
      ∀ a : ℕ, a ≤ m.factorization p + 1 → p ^ a ∣ Nat.totient m) :
    smoothPart (shiftedTotient m) y = smoothPart m y := by
  rw [smoothPart, smoothPart,
    smoothFactorization_shiftedTotient_eq hm hφ]

/-- A prime larger than the smoothness cutoff contributes nothing to the
smooth factorization of a product. -/
lemma factorization_mul_prime_eq_of_le_lt {m p q y : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hqy : q ≤ y) (hyp : y < p) :
    (m * p).factorization q = m.factorization q := by
  have hqp : q ≠ p := by omega
  rw [Nat.factorization_mul hm.ne' hp.ne_zero, Finsupp.add_apply]
  simp [hp.factorization, hqp]

/-- Consequently the whole smooth part is unchanged after adjoining a prime
larger than the cutoff. -/
lemma smoothFactorization_mul_prime_eq_of_lt {m p y : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hyp : y < p) :
    smoothFactorization (m * p) y = smoothFactorization m y := by
  ext q
  simp only [smoothFactorization, Finsupp.filter_apply]
  by_cases hqy : q ≤ y
  · simp only [hqy, ↓reduceIte]
    exact factorization_mul_prime_eq_of_le_lt hm hp hqy hyp
  · simp [hqy]

lemma smoothPart_mul_prime_eq_of_lt {m p y : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hyp : y < p) :
    smoothPart (m * p) y = smoothPart m y := by
  rw [smoothPart, smoothPart,
    smoothFactorization_mul_prime_eq_of_lt hm hp hyp]

/-- The smooth part of the shifted value attached to a new large prime is
the smooth part of the cofactor.  This is the exact local statement used by
the collision partition. -/
lemma smoothPart_shiftedTotient_mul_prime_eq {m p y : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hmp : m < p) (hyp : y < p)
    (hφ : ∀ q : ℕ, q.Prime → q ≤ y →
      ∀ a : ℕ, a ≤ m.factorization q + 1 → q ^ a ∣ Nat.totient m) :
    smoothPart (shiftedTotient (m * p)) y = smoothPart m y := by
  have hnot : ¬ p ∣ m := by
    intro hpm
    have : p ≤ m := Nat.le_of_dvd hm hpm
    omega
  have hφmul : ∀ q : ℕ, q.Prime → q ≤ y →
      ∀ a : ℕ, a ≤ (m * p).factorization q + 1 →
        q ^ a ∣ Nat.totient (m * p) := by
    intro q hq hqy a ha
    have hfac := factorization_mul_prime_eq_of_le_lt hm hp hqy hyp
    rw [hfac] at ha
    rw [Nat.mul_comm m p, Nat.totient_mul_of_prime_of_not_dvd hp hnot]
    exact dvd_mul_of_dvd_right (hφ q hq hqy a ha) _
  calc
    smoothPart (shiftedTotient (m * p)) y = smoothPart (m * p) y :=
      smoothPart_shiftedTotient_eq (Nat.mul_pos hm hp.pos) hφmul
    _ = smoothPart m y := smoothPart_mul_prime_eq_of_lt hm hp hyp

end Erdos822
