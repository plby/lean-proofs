/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CommonDivisorResidues

/-!
# The second medium-range residue

For `m=k*r*q`, adjoining the two new primes gives the exact identity

`shiftedTotient m + φ(k) * (r+q-1) = shiftedTotient k * r * q`.

Modulo a common shifted coefficient this determines `r+q` once `r*q` is
known, because B4 makes `φ(k)` invertible.
-/

namespace Erdos822

/-- Two successive applications of the one-prime shifted-totient identity. -/
theorem shiftedTotient_mul_two_primes_add
    {k r q : ℕ} (hr : r.Prime) (hq : q.Prime)
    (hrk : ¬ r ∣ k) (hqkr : ¬ q ∣ k * r) :
    shiftedTotient (k * r * q) + Nat.totient (k * r) +
        Nat.totient k * q =
      shiftedTotient k * r * q := by
  have hqadd := shiftedTotient_mul_prime_add_totient hq hqkr
    (l := k * r)
  have hradd := shiftedTotient_mul_prime_add_totient hr hrk (l := k)
  calc
    shiftedTotient (k * r * q) + Nat.totient (k * r) +
        Nat.totient k * q =
        (shiftedTotient (k * r * q) + Nat.totient (k * r)) +
          Nat.totient k * q := by ring
    _ = shiftedTotient (k * r) * q + Nat.totient k * q := by
      rw [hqadd]
    _ = (shiftedTotient (k * r) + Nat.totient k) * q := by ring
    _ = shiftedTotient k * r * q := by rw [hradd]

/-- Rewriting the intermediate totient gives the symmetric sum/product
form used in the quadratic congruence. -/
theorem shiftedTotient_mul_two_primes_sum_formula
    {k r q : ℕ} (hr : r.Prime) (hq : q.Prime)
    (hrk : ¬ r ∣ k) (hqkr : ¬ q ∣ k * r) :
    shiftedTotient (k * r * q) +
        Nat.totient k * (r + q - 1) =
      shiftedTotient k * r * q := by
  have hbase := shiftedTotient_mul_two_primes_add hr hq hrk hqkr
  have hphi : Nat.totient (k * r) = (r - 1) * Nat.totient k := by
    rw [Nat.mul_comm k r, Nat.totient_mul_of_prime_of_not_dvd hr hrk]
  have hrsum : r + q - 1 = (r - 1) + q := by
    have hrone : 1 ≤ r := hr.one_le
    omega
  rw [hphi] at hbase
  rw [hrsum]
  nlinarith

/-- If a divisor `h` divides the shifted totient of `k*r*q`, then the sum
`r+q` satisfies the second residue congruence. -/
theorem sum_modEq_of_dvd_shiftedTotient_mul_two_primes
    {h k r q : ℕ} (hr : r.Prime) (hq : q.Prime)
    (hrk : ¬ r ∣ k) (hqkr : ¬ q ∣ k * r)
    (hshift : h ∣ shiftedTotient (k * r * q)) :
    Nat.totient k * (r + q) ≡
      shiftedTotient k * (r * q) + Nat.totient k [MOD h] := by
  have hformula := shiftedTotient_mul_two_primes_sum_formula hr hq hrk hqkr
  have hzero : shiftedTotient (k * r * q) ≡ 0 [MOD h] :=
    hshift.modEq_zero_nat
  have hcong := hzero.add_right (Nat.totient k * (r + q - 1))
  rw [hformula] at hcong
  have hrsum : r + q - 1 + 1 = r + q := by
    have hrone : 1 ≤ r := hr.one_le
    omega
  have hleft : Nat.totient k * (r + q - 1) + Nat.totient k =
      Nat.totient k * (r + q) := by
    calc
      Nat.totient k * (r + q - 1) + Nat.totient k =
          Nat.totient k * ((r + q - 1) + 1) := by ring
      _ = Nat.totient k * (r + q) := by rw [hrsum]
  have hadd := hcong.add_right (Nat.totient k)
  simpa [hleft, Nat.mul_assoc] using hadd.symm

/-- A divisor of a supported common shifted coefficient supplies the second
sum residue for a B4 cofactor. -/
theorem sum_modEq_of_supported_commonDivisor
    {h m m' k r q : ℕ}
    (hr : r.Prime) (hq : q.Prime)
    (hrk : ¬ r ∣ k) (hqkr : ¬ q ∣ k * r)
    (hh : h ∣ shiftedCoefficientGcd m m')
    (hmul : m = k * r * q) :
    Nat.totient k * (r + q) ≡
      shiftedTotient k * (r * q) + Nat.totient k [MOD h] := by
  have hshift : h ∣ shiftedTotient (k * r * q) := by
    rw [← hmul]
    exact dvd_trans hh (by
      unfold shiftedCoefficientGcd
      exact Nat.gcd_dvd_left _ _)
  exact sum_modEq_of_dvd_shiftedTotient_mul_two_primes
    hr hq hrk hqkr hshift

/-- With `k,m',h` fixed, the second congruence and the already determined
product imply that any two supported B4 pairs have the same sum residue. -/
theorem cofactorSums_modEq_of_supported_commonDivisor
    {N x h m₁ m₂ m' k r₁ q₁ r₂ q₂ : ℕ}
    (hm₁ : m₁ ∈ coprimeTotientOddCofactors N)
    (hm₂ : m₂ ∈ coprimeTotientOddCofactors N)
    (hm' : 0 < m')
    (hlarge₁ : ∀ p ∈ outerPrimes x m₁, m₁ < p)
    (hlarge₂ : ∀ p ∈ outerPrimes x m₂, m₂ < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne₁ : (outerCollisionPairs x m₁ m').Nonempty)
    (hne₂ : (outerCollisionPairs x m₂ m').Nonempty)
    (hh₁ : h ∣ shiftedCoefficientGcd m₁ m')
    (hh₂ : h ∣ shiftedCoefficientGcd m₂ m')
    (hmul₁ : m₁ = k * r₁ * q₁)
    (hmul₂ : m₂ = k * r₂ * q₂)
    (hr₁ : r₁.Prime) (hq₁ : q₁.Prime)
    (hr₂ : r₂.Prime) (hq₂ : q₂.Prime)
    (hr₁k : ¬ r₁ ∣ k) (hq₁kr₁ : ¬ q₁ ∣ k * r₁)
    (hr₂k : ¬ r₂ ∣ k) (hq₂kr₂ : ¬ q₂ ∣ k * r₂) :
    r₁ + q₁ ≡ r₂ + q₂ [MOD h] := by
  have hprod : r₁ * q₁ ≡ r₂ * q₂ [MOD h] :=
    cofactorProducts_modEq_of_supported_commonDivisor
      hm₁ hm₂ hm' hlarge₁ hlarge₂ hlarge' hne₁ hne₂
      hh₁ hh₂ hmul₁ hmul₂
  have hsum₁ := sum_modEq_of_supported_commonDivisor
    hr₁ hq₁ hr₁k hq₁kr₁ hh₁ hmul₁
  have hsum₂ := sum_modEq_of_supported_commonDivisor
    hr₂ hq₂ hr₂k hq₂kr₂ hh₂ hmul₂
  have hrhs :
      shiftedTotient k * (r₁ * q₁) + Nat.totient k ≡
        shiftedTotient k * (r₂ * q₂) + Nat.totient k [MOD h] :=
    (hprod.mul_left (shiftedTotient k)).add_right (Nat.totient k)
  have hphi :
      Nat.totient k * (r₁ + q₁) ≡
        Nat.totient k * (r₂ + q₂) [MOD h] :=
    hsum₁.trans (hrhs.trans hsum₂.symm)
  have hkdiv : k ∣ m₁ := by
    rw [hmul₁]
    exact ⟨r₁ * q₁, by ring⟩
  have hcop : Nat.Coprime h (Nat.totient k) :=
    Nat.Coprime.of_dvd_left hh₁
      (shiftedCoefficientGcd_coprime_totient_leftFactor_of_coprime_totient
        hkdiv (mem_coprimeTotientOddCofactors_iff.mp hm₁).2)
  exact Nat.ModEq.cancel_left_of_coprime hcop hphi

end Erdos822
