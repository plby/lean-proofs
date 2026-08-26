/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The prime exponents used by the exact-cardinality construction.
Informal source: Section 6.2 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.SeedExceptions
import ErdosProblems.Erdos1189.PrimeBudget

namespace Erdos1189

open Finset

lemma factorization_prod_primes {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) (p : ℕ) :
    (∏ q ∈ D, q).factorization p = if p ∈ D then 1 else 0 := by
  induction D using Finset.induction with
  | empty => simp
  | @insert q D hq ih =>
      have hqP : q.Prime := hD q (mem_insert_self _ _)
      have hDP : ∀ r ∈ D, r.Prime := fun r hr => hD r (mem_insert_of_mem hr)
      rw [prod_insert hq, Nat.factorization_mul hqP.ne_zero
        (prod_ne_zero_iff.mpr (fun r hr => (hDP r hr).ne_zero))]
      simp only [Finsupp.add_apply, hqP.factorization, Finsupp.single_apply, ih hDP]
      by_cases hpq : p = q
      · subst p
        simp [hq]
      · simp [hpq, Ne.symm hpq]

def frameInteger (P : ℕ) (D : Finset ℕ) : ℕ :=
  (∏ p ∈ Nat.primesLE P, p) * ∏ p ∈ D, p

lemma frameInteger_ne_zero {P : ℕ} {D : Finset ℕ} (hD : D ⊆ Nat.primesLE P) :
    frameInteger P D ≠ 0 := by
  apply mul_ne_zero
  · exact prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primesLE hp).ne_zero)
  · exact prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primesLE (hD hp)).ne_zero)

lemma frameInteger_factorization {P : ℕ} {D : Finset ℕ} (hD : D ⊆ Nat.primesLE P) (p : ℕ) :
    (frameInteger P D).factorization p =
      (if p ∈ Nat.primesLE P then 1 else 0) + (if p ∈ D then 1 else 0) := by
  rw [frameInteger, Nat.factorization_mul
    (prod_ne_zero_iff.mpr (fun q hq => (Nat.prime_of_mem_primesLE hq).ne_zero))
    (prod_ne_zero_iff.mpr (fun q hq => (Nat.prime_of_mem_primesLE (hD hq)).ne_zero))]
  simp only [Finsupp.add_apply,
    factorization_prod_primes (fun q hq => Nat.prime_of_mem_primesLE hq),
    factorization_prod_primes (fun q hq => Nat.prime_of_mem_primesLE (hD hq))]

lemma frameInteger_primeFactors {P : ℕ} {D : Finset ℕ} (hD : D ⊆ Nat.primesLE P) :
    (frameInteger P D).primeFactors = Nat.primesLE P := by
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, frameInteger_factorization hD]
  by_cases hp : p ∈ Nat.primesLE P
  · simp [hp]
  · have hpD : p ∉ D := fun h => hp (hD h)
    simp [hp, hpD]

lemma frameInteger_exponent_le_two {P : ℕ} {D : Finset ℕ} (hD : D ⊆ Nat.primesLE P) (p : ℕ) :
    (frameInteger P D).factorization p ≤ 2 := by
  rw [frameInteger_factorization hD]
  split_ifs <;> omega

lemma frameInteger_weight {P : ℕ} {D : Finset ℕ} (hD : D ⊆ Nat.primesLE P) :
    simpsonWeight (frameInteger P D) = primeWeightSum P + ∑ p ∈ D, (p - 1) := by
  rw [frameInteger, simpsonWeight_mul
    (prod_ne_zero_iff.mpr (fun q hq => (Nat.prime_of_mem_primesLE hq).ne_zero))
    (prod_ne_zero_iff.mpr (fun q hq => (Nat.prime_of_mem_primesLE (hD hq)).ne_zero)),
    simpsonWeight_prime_product (fun q hq => Nat.prime_of_mem_primesLE hq),
    simpsonWeight_prime_product (fun q hq => Nat.prime_of_mem_primesLE (hD hq))]
  rfl

lemma squarefree_seed_dvd_frameInteger {P : ℕ} {D : Finset ℕ} (hD : D ⊆ Nat.primesLE P)
    {d : ℕ} (hsf : Squarefree d) (hsupport : ∀ p ∈ d.primeFactors, p ≤ P) :
    d ∣ frameInteger P D := by
  have hsub : d.primeFactors ⊆ (frameInteger P D).primeFactors := by
    rw [frameInteger_primeFactors hD]
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨hsupport p hp, Nat.prime_of_mem_primeFactors hp⟩
  rw [← Nat.prod_primeFactors_of_squarefree hsf]
  exact (prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd _)

lemma frameInteger_terminal_exponent {P B : ℕ} {D : Finset ℕ} (hP : P.Prime)
    (hB : B < P) (hD : D ⊆ Nat.primesLE B) : (frameInteger P D).factorization P = 1 := by
  have hDP : D ⊆ Nat.primesLE P := fun q hq => Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE (hD hq)).trans hB.le, Nat.prime_of_mem_primesLE (hD hq)⟩
  have hPD : P ∉ D := by
    intro hp
    have := Nat.le_of_mem_primesLE (hD hp)
    omega
  simp [frameInteger_factorization hDP, hP, Nat.mem_primesLE, hPD]

lemma frameInteger_prime_power_bound {P B : ℕ} {D : Finset ℕ}
    (hB : B ≤ P) (hD : D ⊆ Nat.primesLE B) {p : ℕ} (hp : p ∈ Nat.primesLE P) :
    p ^ (frameInteger P D).factorization p ≤ max P (B ^ 2) := by
  have hDP : D ⊆ Nat.primesLE P := fun q hq => Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE (hD hq)).trans hB, Nat.prime_of_mem_primesLE (hD hq)⟩
  rw [frameInteger_factorization hDP, if_pos hp]
  by_cases hpD : p ∈ D
  · rw [if_pos hpD]
    exact (Nat.pow_le_pow_left (Nat.le_of_mem_primesLE (hD hpD)) 2).trans (le_max_right _ _)
  · rw [if_neg hpD]
    simpa using (Nat.le_of_mem_primesLE hp).trans (le_max_left P (B ^ 2))

end Erdos1189
