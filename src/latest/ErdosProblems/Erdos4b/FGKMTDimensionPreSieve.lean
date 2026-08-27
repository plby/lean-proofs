/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPreSieveAdmissible
import ErdosProblems.Erdos4b.Base

/-! # The actual dimension-dependent small-prime modulus -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def dimensionPreSievePrimes (k B : ℕ) : Finset ℕ :=
  (Nat.primesLE (2 * k ^ 2)).filter (fun p => p ≠ B)

def dimensionPreSieveModulus (k B : ℕ) : ℕ := ∏ p ∈ dimensionPreSievePrimes k B, p

theorem mem_dimensionPreSievePrimes {k B p : ℕ} :
    p ∈ dimensionPreSievePrimes k B ↔ p.Prime ∧ p ≤ 2 * k ^ 2 ∧ p ≠ B := by
  simp only [dimensionPreSievePrimes, Finset.mem_filter, Nat.mem_primesLE]
  tauto

theorem dimensionPreSieveModulus_pos (k B : ℕ) : 0 < dimensionPreSieveModulus k B := by
  exact Finset.prod_pos fun p hp => (mem_dimensionPreSievePrimes.mp hp).1.pos

theorem dimensionPreSieveModulus_coprime {k B : ℕ} (hB : B = 1 ∨ B.Prime) :
    B.Coprime (dimensionPreSieveModulus k B) := by
  rcases hB with rfl | hB
  · exact Nat.coprime_one_left _
  · apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    have h := mem_dimensionPreSievePrimes.mp hp
    exact (Nat.coprime_primes hB h.1).mpr (Ne.symm h.2.2)

theorem small_prime_dvd_dimensionPreSieve {k B p : ℕ}
    (hp : p.Prime) (hpk : p ≤ 2 * k ^ 2) : p ∣ B * dimensionPreSieveModulus k B := by
  by_cases heq : p = B
  · subst p
    exact dvd_mul_right B _
  · have hmem := mem_dimensionPreSievePrimes.mpr ⟨hp, hpk, heq⟩
    have hdiv : p ∣ dimensionPreSieveModulus k B := Finset.dvd_prod_of_mem _ hmem
    exact dvd_mul_of_dvd_right hdiv B

theorem prime_dvd_dimensionPreSieve_le {k B p : ℕ}
    (hp : p.Prime) (hd : p ∣ dimensionPreSieveModulus k B) : p ≤ 2 * k ^ 2 := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  have h := mem_dimensionPreSievePrimes.mp hq
  exact (Nat.le_of_dvd h.1.pos hpq).trans h.2.1

theorem prime_coprime_dimensionPreSieve {k B Q : ℕ}
    (hQ : Q.Prime) (hkQ : 2 * k ^ 2 < Q) : Q.Coprime (dimensionPreSieveModulus k B) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  have h := mem_dimensionPreSievePrimes.mp hp
  exact (Nat.coprime_primes hQ h.1).mpr (by omega)

theorem dimensionPreSieveModulus_le_exp (k B : ℕ) :
    (dimensionPreSieveModulus k B : ℝ) ≤ Real.exp (8 * (k : ℝ) ^ 2) := by
  have hprim : dimensionPreSieveModulus k B ≤ primorial (2 * k ^ 2) :=
    Erdos4b.primeProduct_le_primorial (Finset.filter_subset _ _)
  have hpow : dimensionPreSieveModulus k B ≤ 4 ^ (2 * k ^ 2) :=
    hprim.trans (primorial_le_four_pow _)
  calc
    _ ≤ (4 : ℝ) ^ (2 * k ^ 2) := by exact_mod_cast hpow
    _ ≤ Real.exp 4 ^ (2 * k ^ 2) :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 4]) _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

theorem exists_dimensionPreSieveCondition {ι : Type*} [Fintype ι]
    (k B : ℕ) (h : ι → ℕ) (hadm : BoundedGaps.IsAdmissible (Finset.univ.image h)) :
    ∃ n : ℤ, preSieveCondition (dimensionPreSieveModulus k B) (fun i => (h i : ℤ)) n :=
  exists_preSieveCondition_of_admissible h (dimensionPreSievePrimes k B) hadm
    (fun _p hp => (mem_dimensionPreSievePrimes.mp hp).1)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.dimensionPreSieveModulus_coprime
#print axioms Erdos4b.FGKMT.dimensionPreSieveModulus_le_exp
#print axioms Erdos4b.FGKMT.exists_dimensionPreSieveCondition
