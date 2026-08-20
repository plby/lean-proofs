/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.LargePrimeResidueBound

/-!
# Residue classes forced by a shifted-totient divisor

For a new prime factor q the identity

shiftedTotient (l * q) + phi(l) = shiftedTotient l * q

turns divisibility by a prime p into one congruence class for q.
The coefficient is cancellable whenever p does not divide l: if it were
divisible by p, the same identity would force p to divide phi(l) and hence l.
-/

namespace Erdos822

/-- Additive form of the linear shifted-totient identity. -/
theorem shiftedTotient_mul_prime_add_totient
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

/-- If p does not divide l and p divides the shifted totient after
adjoining a new prime q, then p cannot divide the linear coefficient. -/
theorem not_dvd_shiftedTotient_of_dvd_shiftedTotient_mul_prime
    {l p q : ℕ} (hq : q.Prime) (hql : ¬ q ∣ l)
    (hpl : ¬ p ∣ l) (hdiv : p ∣ shiftedTotient (l * q)) :
    ¬ p ∣ shiftedTotient l := by
  intro hcoef
  have hadd := shiftedTotient_mul_prime_add_totient hq hql
  have hmul : p ∣ shiftedTotient l * q :=
    dvd_mul_of_dvd_left hcoef q
  have hsum : p ∣ shiftedTotient (l * q) + Nat.totient l := by
    rw [hadd]
    exact hmul
  have hphi : p ∣ Nat.totient l :=
    (Nat.dvd_add_iff_right hdiv).mpr hsum
  have hshift : p ∣ l + Nat.totient l := by
    simpa [shiftedTotient] using hcoef
  exact hpl ((Nat.dvd_add_iff_left hphi).mpr hshift)

/-- Two new primes for which the same prime p divides the shifted
totient lie in the same residue class modulo p, provided p does not divide l. -/
theorem modEq_of_dvd_shiftedTotient_mul_prime
    {l p q q₀ : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hq₀ : q₀.Prime)
    (hql : ¬ q ∣ l) (hq₀l : ¬ q₀ ∣ l)
    (hpl : ¬ p ∣ l)
    (hdiv : p ∣ shiftedTotient (l * q))
    (hdiv₀ : p ∣ shiftedTotient (l * q₀)) :
    q ≡ q₀ [MOD p] := by
  have hcoef :
      ¬ p ∣ shiftedTotient l :=
    not_dvd_shiftedTotient_of_dvd_shiftedTotient_mul_prime
      hq hql hpl hdiv
  have hadd := shiftedTotient_mul_prime_add_totient hq hql
  have hadd₀ := shiftedTotient_mul_prime_add_totient hq₀ hq₀l
  have hmod :
      shiftedTotient l * q ≡ Nat.totient l [MOD p] := by
    rw [← hadd]
    simpa using hdiv.modEq_zero_nat.add_right (Nat.totient l)
  have hmod₀ :
      shiftedTotient l * q₀ ≡ Nat.totient l [MOD p] := by
    rw [← hadd₀]
    simpa using hdiv₀.modEq_zero_nat.add_right (Nat.totient l)
  exact Nat.ModEq.cancel_left_of_coprime
    ((hp.coprime_iff_not_dvd).2 hcoef) (hmod.trans hmod₀.symm)

/-- Large primes which make p divide the shifted totient of k*r*q. -/
def shiftedDivisibleLargePrimes (N p k r : ℕ) : Finset ℕ :=
  (largePrimes N).filter fun q => p ∣ shiftedTotient (k * r * q)

@[simp]
theorem mem_shiftedDivisibleLargePrimes_iff
    {N p k r q : ℕ} :
    q ∈ shiftedDivisibleLargePrimes N p k r ↔
      q ∈ largePrimes N ∧ p ∣ shiftedTotient (k * r * q) := by
  simp [shiftedDivisibleLargePrimes]

/-- For fixed k,r, a nonempty shifted-divisible large-prime fiber is
contained in one large-prime residue class modulo p. -/
theorem shiftedDivisibleLargePrimes_subset_largePrimeResidueClass_of_nonempty
    {N p k r y : ℕ} (hN : 2 ≤ N) (hp : p.Prime)
    (hk : k ∈ oddSmallFactors N) (hr : r ∈ middlePrimes N)
    (hpk : ¬ p ∣ k) (hpr : ¬ p ∣ r) (hy : y < N ^ 21)
    (hne : (shiftedDivisibleLargePrimes N p k r).Nonempty) :
    let q₀ := (shiftedDivisibleLargePrimes N p k r).min' hne
    shiftedDivisibleLargePrimes N p k r ⊆
      largePrimeResidueClass N p q₀ y := by
  classical
  let Q := shiftedDivisibleLargePrimes N p k r
  let q₀ := Q.min' hne
  dsimp only
  have hq₀mem : q₀ ∈ Q := Finset.min'_mem Q hne
  have hq₀data := mem_shiftedDivisibleLargePrimes_iff.mp hq₀mem
  have hpl : ¬ p ∣ k * r := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hpk h
    · exact hpr h
  intro q hq
  have hqdata := mem_shiftedDivisibleLargePrimes_iff.mp hq
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
    have hle : q ≤ k * r :=
      Nat.le_of_dvd hkrpos h
    omega
  have hq₀l : ¬ q₀ ∣ k * r := by
    intro h
    have hle : q₀ ≤ k * r :=
      Nat.le_of_dvd hkrpos h
    omega
  have hmod :
      q ≡ q₀ [MOD p] :=
    modEq_of_dvd_shiftedTotient_mul_prime hp
      (mem_largePrimes_iff.mp hqdata.1).2.2
      (mem_largePrimes_iff.mp hq₀data.1).2.2
      hql hq₀l hpl hqdata.2 hq₀data.2
  rw [mem_largePrimeResidueClass_iff]
  refine ⟨hqdata.1, ?_, ?_⟩
  · have hqL := (mem_largePrimes_iff.mp hqdata.1).1
    omega
  · exact hmod

end Erdos822
