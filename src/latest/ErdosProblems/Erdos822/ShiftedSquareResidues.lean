/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.IntegerResidueBlocks
import ErdosProblems.Erdos822.ShiftedTotientResidues

/-!
# Prime-square residue classes for shifted totients

If a modulus is coprime to the linear coefficient, divisibility of the
shifted totient after adjoining a new prime forces one residue class for
that prime.  Applying this with a prime square is the local input for
removing repeated large prime factors from the cofactor coefficients.
-/

namespace Erdos822

/-- Divisibility by an arbitrary modulus determines the new prime modulo
that modulus whenever the old shifted coefficient is invertible. -/
theorem modEq_of_dvd_shiftedTotient_mul_prime_of_coprime
    {l d q q₀ : ℕ}
    (hq : q.Prime) (hq₀ : q₀.Prime)
    (hql : ¬ q ∣ l) (hq₀l : ¬ q₀ ∣ l)
    (hcoef : Nat.Coprime d (shiftedTotient l))
    (hdiv : d ∣ shiftedTotient (l * q))
    (hdiv₀ : d ∣ shiftedTotient (l * q₀)) :
    q ≡ q₀ [MOD d] := by
  have hadd := shiftedTotient_mul_prime_add_totient hq hql
  have hadd₀ := shiftedTotient_mul_prime_add_totient hq₀ hq₀l
  have hmod :
      shiftedTotient l * q ≡ Nat.totient l [MOD d] := by
    rw [← hadd]
    simpa using hdiv.modEq_zero_nat.add_right (Nat.totient l)
  have hmod₀ :
      shiftedTotient l * q₀ ≡ Nat.totient l [MOD d] := by
    rw [← hadd₀]
    simpa using hdiv₀.modEq_zero_nat.add_right (Nat.totient l)
  exact Nat.ModEq.cancel_left_of_coprime hcoef
    (hmod.trans hmod₀.symm)

/-- Large primes whose adjunction makes a fixed prime square divide the
shifted totient. -/
def shiftedSquareDivisibleLargePrimes
    (N p k r : ℕ) : Finset ℕ :=
  (largePrimes N).filter fun q =>
    p ^ 2 ∣ shiftedTotient (k * r * q)

@[simp]
theorem mem_shiftedSquareDivisibleLargePrimes_iff
    {N p k r q : ℕ} :
    q ∈ shiftedSquareDivisibleLargePrimes N p k r ↔
      q ∈ largePrimes N ∧
        p ^ 2 ∣ shiftedTotient (k * r * q) := by
  simp [shiftedSquareDivisibleLargePrimes]

/-- For fixed k,r, a nonempty prime-square shifted-divisibility fiber is
contained in one large-prime residue class modulo p². -/
theorem shiftedSquareDivisibleLargePrimes_subset_largePrimeResidueClass
    {N p k r y : ℕ} (hN : 2 ≤ N) (hp : p.Prime)
    (hk : k ∈ oddSmallFactors N) (hr : r ∈ middlePrimes N)
    (hpk : ¬ p ∣ k) (hpr : ¬ p ∣ r) (hy : y < N ^ 21)
    (hne : (shiftedSquareDivisibleLargePrimes N p k r).Nonempty) :
    let q₀ := (shiftedSquareDivisibleLargePrimes N p k r).min' hne
    shiftedSquareDivisibleLargePrimes N p k r ⊆
      largePrimeResidueClass N (p ^ 2) q₀ y := by
  classical
  let Q := shiftedSquareDivisibleLargePrimes N p k r
  let q₀ := Q.min' hne
  dsimp only
  have hq₀mem : q₀ ∈ Q := Finset.min'_mem Q hne
  have hq₀data := mem_shiftedSquareDivisibleLargePrimes_iff.mp hq₀mem
  have hpl : ¬ p ∣ k * r := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hpk h
    · exact hpr h
  intro q hq
  have hqdata := mem_shiftedSquareDivisibleLargePrimes_iff.mp hq
  have hsep :
      k * r < q :=
    (oddCofactorTriples_separated hN
      (show (k, r, q) ∈ oddCofactorTriples N by
        rw [mem_oddCofactorTriples_iff]
        exact ⟨hk, hr, hqdata.1⟩)).2.2
  have hsep₀ :
      k * r < q₀ :=
    (oddCofactorTriples_separated hN
      (show (k, r, q₀) ∈ oddCofactorTriples N by
        rw [mem_oddCofactorTriples_iff]
        exact ⟨hk, hr, hq₀data.1⟩)).2.2
  have hkrpos : 0 < k * r :=
    Nat.mul_pos (oddSmallFactors_pos hk)
      (mem_middlePrimes_iff.mp hr).2.2.pos
  have hql : ¬ q ∣ k * r := by
    intro h
    have hle : q ≤ k * r := Nat.le_of_dvd hkrpos h
    omega
  have hq₀l : ¬ q₀ ∣ k * r := by
    intro h
    have hle : q₀ ≤ k * r := Nat.le_of_dvd hkrpos h
    omega
  have hdivp : p ∣ shiftedTotient (k * r * q) :=
    dvd_trans (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)) hqdata.2
  have hcoefNot : ¬ p ∣ shiftedTotient (k * r) :=
    not_dvd_shiftedTotient_of_dvd_shiftedTotient_mul_prime
      (mem_largePrimes_iff.mp hqdata.1).2.2 hql hpl hdivp
  have hcoef : Nat.Coprime (p ^ 2) (shiftedTotient (k * r)) :=
    (hp.coprime_pow_of_not_dvd hcoefNot).symm
  have hmod :
      q ≡ q₀ [MOD p ^ 2] :=
    modEq_of_dvd_shiftedTotient_mul_prime_of_coprime
      (mem_largePrimes_iff.mp hqdata.1).2.2
      (mem_largePrimes_iff.mp hq₀data.1).2.2
      hql hq₀l hcoef hqdata.2 hq₀data.2
  rw [mem_largePrimeResidueClass_iff]
  refine ⟨hqdata.1, ?_, ?_⟩
  · have hqL := (mem_largePrimes_iff.mp hqdata.1).1
    omega
  · exact hmod

end Erdos822
