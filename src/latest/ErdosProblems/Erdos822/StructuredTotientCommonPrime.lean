/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.StructuredTotientFormula

/-!
# Common primes of a structured cofactor and its totient

For `m=k*r*q`, primality of `r,q` and totient multiplicativity reduce a
B4 failure to finitely many explicit divisibility channels.  Subsequent
weighted incidence estimates can treat those channels separately.
-/

namespace Erdos822

/-- Raw nine-case decomposition of a prime common to `k*r*q` and its
totient.  The first disjunction records where the prime divides the
cofactor, and the second where it divides the factored totient. -/
theorem prime_dvd_structured_product_and_totient_cases
    {p k r q : ℕ} (hp : p.Prime) (hr : r.Prime) (hq : q.Prime)
    (hrk : ¬ r ∣ k) (hqkr : ¬ q ∣ k * r)
    (hpm : p ∣ k * r * q) (hpφ : p ∣ Nat.totient (k * r * q)) :
    (p ∣ k ∨ p = r ∨ p = q) ∧
      (p ∣ Nat.totient k ∨ p ∣ r - 1 ∨ p ∣ q - 1) := by
  constructor
  · rcases hp.dvd_mul.mp hpm with hpk | hpq
    · rcases hp.dvd_mul.mp hpk with hpk | hpr
      · exact Or.inl hpk
      · exact Or.inr (Or.inl
          (((Nat.dvd_prime hr).mp hpr).resolve_left hp.ne_one))
    · exact Or.inr (Or.inr
        (((Nat.dvd_prime hq).mp hpq).resolve_left hp.ne_one))
  · rw [totient_mul_two_primes hr hq hrk hqkr] at hpφ
    rcases hp.dvd_mul.mp hpφ with hleft | hpq
    · rcases hp.dvd_mul.mp hleft with hpk | hpr
      · exact Or.inl hpk
      · exact Or.inr (Or.inl hpr)
    · exact Or.inr (Or.inr hpq)

/-- Expanded channel form, convenient for finite union bounds. -/
theorem prime_dvd_structured_product_and_totient_nine_cases
    {p k r q : ℕ} (hp : p.Prime) (hr : r.Prime) (hq : q.Prime)
    (hrk : ¬ r ∣ k) (hqkr : ¬ q ∣ k * r)
    (hpm : p ∣ k * r * q) (hpφ : p ∣ Nat.totient (k * r * q)) :
    (p ∣ k ∧ p ∣ Nat.totient k) ∨
    (p ∣ k ∧ p ∣ r - 1) ∨
    (p ∣ k ∧ p ∣ q - 1) ∨
    (p = r ∧ p ∣ Nat.totient k) ∨
    (p = r ∧ p ∣ r - 1) ∨
    (p = r ∧ p ∣ q - 1) ∨
    (p = q ∧ p ∣ Nat.totient k) ∨
    (p = q ∧ p ∣ r - 1) ∨
    (p = q ∧ p ∣ q - 1) := by
  rcases prime_dvd_structured_product_and_totient_cases
      hp hr hq hrk hqkr hpm hpφ with ⟨hm, hφ⟩
  rcases hm with hpk | hpr | hpq <;>
    rcases hφ with hpK | hpR | hpQ
  · exact Or.inl ⟨hpk, hpK⟩
  · exact Or.inr (Or.inl ⟨hpk, hpR⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hpk, hpQ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hpr, hpK⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpr, hpR⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hpr, hpQ⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨hpq, hpK⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨hpq, hpR⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr ⟨hpq, hpQ⟩)))))))

/-- After using the size separation `k<r<q`, only four genuine B4-failure
channels remain. -/
theorem prime_dvd_structured_product_and_totient_four_cases
    {p k r q : ℕ} (hp : p.Prime) (hr : r.Prime) (hq : q.Prime)
    (hrk : ¬ r ∣ k) (hqkr : ¬ q ∣ k * r)
    (hk : 0 < k) (hkr : k < r) (hrq : r < q)
    (hpm : p ∣ k * r * q) (hpφ : p ∣ Nat.totient (k * r * q)) :
    (p ∣ k ∧ p ∣ Nat.totient k) ∨
    (p ∣ k ∧ p ∣ r - 1) ∨
    (p ∣ k ∧ p ∣ q - 1) ∨
    (p = r ∧ r ∣ q - 1) := by
  rcases prime_dvd_structured_product_and_totient_nine_cases
      hp hr hq hrk hqkr hpm hpφ with
    h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases h with ⟨hpEq, hrφ⟩
    subst p
    exfalso
    exact (Nat.not_dvd_of_pos_of_lt (Nat.totient_pos.2 hk)
      (k.totient_le.trans_lt hkr)) hrφ
  · rcases h with ⟨hpEq, hrr⟩
    subst p
    exfalso
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < r - 1)
      (by omega : r - 1 < r)) hrr
  · rcases h with ⟨hpEq, hrqPred⟩
    subst p
    exact Or.inr (Or.inr (Or.inr ⟨rfl, hrqPred⟩))
  · rcases h with ⟨hpEq, hqφ⟩
    subst p
    exfalso
    exact (Nat.not_dvd_of_pos_of_lt (Nat.totient_pos.2 hk)
      ((k.totient_le.trans_lt hkr).trans hrq)) hqφ
  · rcases h with ⟨hpEq, hqr⟩
    subst p
    exfalso
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < r - 1)
      (by omega : r - 1 < q)) hqr
  · rcases h with ⟨hpEq, hqq⟩
    subst p
    exfalso
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < q - 1)
      (by omega : q - 1 < q)) hqq

end Erdos822
