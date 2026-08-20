/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedRoughSieve

/-!
# Erdős Problem 446: exact small-prime valuation cells

For a positive squarefree integer `c`, all of whose prime factors are at
most `N`, the set `roughFactorEvent N c` is precisely the CRT cell on which
the primes dividing `c` have valuation one and all other primes at most `N`
have valuation zero.  Its density is therefore the exact quantity

`smallPrimeEulerDensity N / c`.

The second half of the file records the important arithmetic consequence:
inside this cell, the positive divisors at most `N` are exactly the positive
divisors of `c` at most `N`.
-/

namespace Erdos446

open Filter Finset Set Real
open scoped BigOperators Topology

/-- The exact small-prime valuation condition belonging to `c`: a prime at
most `N` occurs to exponent exactly one if it divides `c`, and to exponent
zero otherwise. -/
def ExactSmallPrimeValuations (N c m : ℕ) : Prop :=
  ∀ p : PrimeIndex N,
    if p.1 ∈ c.primeFactors then
      p.1 ∣ m ∧ ¬p.1 * p.1 ∣ m
    else
      ¬p.1 ∣ m

/-- The exact CRT valuation cell represented by a positive squarefree
integer `c`.  The rough quotient formulation gives a canonical quotient and
an exact density theorem. -/
def exactValuationCell (N c : ℕ) : Set ℕ :=
  roughFactorEvent N c

theorem mem_exactValuationCell_iff {N c m : ℕ} :
    m ∈ exactValuationCell N c ↔ c ∣ m ∧ roughAt N (m / c) := by
  rfl

private theorem prime_mem_primesUpTo_of_le {N p : ℕ}
    (hp : p.Prime) (hpN : p ≤ N) : p ∈ primesUpTo N := by
  rw [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hp.two_le, hpN⟩, hp⟩

/-- In an exact valuation cell, the ordinary small-prime divisibility
pattern is exactly the support of `c`. -/
theorem primePattern_eq_supportPattern_of_mem_exactValuationCell
    {N c m : ℕ} (hc : 0 < c) (hcut : PrimeFactorsAtMost N c)
    (hm : m ∈ exactValuationCell N c) :
    primePattern N m = supportPattern N c := by
  ext p
  rw [mem_primePattern_iff, mem_supportPattern_iff]
  constructor
  · intro hpm
    have hmEq : m = c * (m / c) := (Nat.mul_div_cancel' hm.1).symm
    have hpMul : p.1 ∣ c ∨ p.1 ∣ m / c := by
      rw [hmEq] at hpm
      exact (primeIndex_prime p).dvd_mul.mp hpm
    rcases hpMul with hpc | hpq
    · exact Nat.mem_primeFactors.mpr ⟨(primeIndex_prime p), hpc, hc.ne'⟩
    · exact (roughAt_iff.mp hm.2 p.1 p.2 hpq).elim
  · intro hpc
    have hpcDvd : p.1 ∣ c := Nat.dvd_of_mem_primeFactors hpc
    exact hpcDvd.trans hm.1

private theorem prime_square_not_dvd_fixedFactor
    {p c : ℕ} (hp : p.Prime) (hc : Squarefree c)
    (hpc : p ∣ c) : ¬p * p ∣ c := by
  intro hppc
  exact hp.not_isUnit (hc p hppc)

/-- The rough-factor cell really is the stated exact `p`-adic valuation
cell.  This is the finite CRT characterization used in the fixed
multiplicity construction. -/
theorem exactSmallPrimeValuations_of_mem_exactValuationCell
    {N c m : ℕ} (hcpos : 0 < c) (hcsq : Squarefree c)
    (hcut : PrimeFactorsAtMost N c)
    (hm : m ∈ exactValuationCell N c) :
    ExactSmallPrimeValuations N c m := by
  intro p
  split_ifs with hpc
  · have hpDvdC : p.1 ∣ c := Nat.dvd_of_mem_primeFactors hpc
    refine ⟨hpDvdC.trans hm.1, ?_⟩
    intro hppM
    have hmEq : m = c * (m / c) := (Nat.mul_div_cancel' hm.1).symm
    obtain ⟨a, ha⟩ := hpDvdC
    have hpDvdRest : p.1 ∣ a * (m / c) := by
      have hmForm : m = p.1 * (a * (m / c)) := by
        calc
          m = c * (m / c) := hmEq
          _ = p.1 * (a * (m / c)) := by rw [ha]; ring
      apply (Nat.mul_dvd_mul_iff_left (primeIndex_pos p)).mp
      rw [hmForm] at hppM
      simpa [mul_assoc] using hppM
    rcases (primeIndex_prime p).dvd_mul.mp hpDvdRest with hpa | hpq
    · have hppC : p.1 * p.1 ∣ c := by
        rw [ha]
        exact Nat.mul_dvd_mul_left p.1 hpa
      exact (prime_square_not_dvd_fixedFactor
        (primeIndex_prime p) hcsq (Nat.dvd_of_mem_primeFactors hpc)) hppC
    · exact (roughAt_iff.mp hm.2 p.1 p.2 hpq).elim
  · intro hpm
    have hpattern := primePattern_eq_supportPattern_of_mem_exactValuationCell
      hcpos hcut hm
    have : p ∈ supportPattern N c := by
      rw [← hpattern, mem_primePattern_iff]
      exact hpm
    exact hpc (mem_supportPattern_iff.mp this)

/-- Conversely, the exact small-prime valuation prescription determines the
rough-factor cell. -/
theorem mem_exactValuationCell_of_exactSmallPrimeValuations
    {N c m : ℕ} (hcpos : 0 < c) (hcsq : Squarefree c)
    (hcut : PrimeFactorsAtMost N c)
    (hval : ExactSmallPrimeValuations N c m) :
    m ∈ exactValuationCell N c := by
  have hpat : primePattern N m = supportPattern N c := by
    ext p
    rw [mem_primePattern_iff, mem_supportPattern_iff]
    by_cases hpc : p.1 ∈ c.primeFactors
    · exact ⟨fun _ ↦ hpc, fun _ ↦ (if_pos hpc ▸ hval p).1⟩
    · have hv := hval p
      rw [if_neg hpc] at hv
      exact ⟨fun hpm ↦ (hv hpm).elim, fun hp ↦ (hpc hp).elim⟩
  have hcm : c ∣ m :=
    dvd_of_primePattern_eq_supportPattern hcsq hcut hpat
  refine ⟨hcm, roughAt_iff.mpr ?_⟩
  intro p hpSmall hpq
  let pN : PrimeIndex N := ⟨p, hpSmall⟩
  by_cases hpc : p ∈ c.primeFactors
  · have hv := hval pN
    rw [if_pos hpc] at hv
    have hpDvdC : p ∣ c := Nat.dvd_of_mem_primeFactors hpc
    obtain ⟨a, ha⟩ := hpDvdC
    have hmEq : m = c * (m / c) := (Nat.mul_div_cancel' hcm).symm
    apply hv.2
    obtain ⟨b, hb⟩ := hpq
    refine ⟨a * b, ?_⟩
    calc
      m = c * (m / c) := hmEq
      _ = (p * a) * (m / c) := congrArg (fun t : ℕ ↦ t * (m / c)) ha
      _ = (p * a) * (p * b) := by rw [hb]
      _ = p * p * (a * b) := by ring
  · have hv := hval pN
    rw [if_neg hpc] at hv
    apply hv
    exact hpq.trans (Nat.div_dvd_of_dvd hcm)

theorem mem_exactValuationCell_iff_exactSmallPrimeValuations
    {N c m : ℕ} (hcpos : 0 < c) (hcsq : Squarefree c)
    (hcut : PrimeFactorsAtMost N c) :
    m ∈ exactValuationCell N c ↔ ExactSmallPrimeValuations N c m := by
  exact ⟨exactSmallPrimeValuations_of_mem_exactValuationCell
      hcpos hcsq hcut,
    mem_exactValuationCell_of_exactSmallPrimeValuations hcpos hcsq hcut⟩

/-- Exact natural density of one squarefree small-prime valuation cell. -/
theorem exactValuationCell_hasDensity (N c : ℕ) (hc : 0 < c) :
    (exactValuationCell N c).HasDensity
      (smallPrimeEulerDensity N / (c : ℝ)) := by
  exact roughFactorEvent_hasDensity N c hc

/-- A positive integer `d ≤ N` is coprime to the rough quotient in an exact
valuation cell. -/
theorem coprime_divisor_roughQuotient_of_le
    {N c m d : ℕ} (hd : 0 < d) (hdN : d ≤ N)
    (hm : m ∈ exactValuationCell N c) :
    d.Coprime (m / c) := by
  by_contra hcop
  obtain ⟨p, hpPrime, hpd, hpq⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpLeD : p ≤ d := Nat.le_of_dvd hd hpd
  have hpN : p ∈ primesUpTo N :=
    prime_mem_primesUpTo_of_le hpPrime (hpLeD.trans hdN)
  exact roughAt_iff.mp hm.2 p hpN hpq

/-- Membership in an exact cell preserves every positive divisor up to the
cutoff. -/
theorem dvd_iff_dvd_fixedFactor_of_mem_exactValuationCell
    {N c m d : ℕ} (hd : 0 < d) (hdN : d ≤ N)
    (hm : m ∈ exactValuationCell N c) :
    d ∣ m ↔ d ∣ c := by
  constructor
  · intro hdm
    have hmEq : m = c * (m / c) := (Nat.mul_div_cancel' hm.1).symm
    rw [hmEq] at hdm
    exact (coprime_divisor_roughQuotient_of_le hd hdN hm).dvd_of_dvd_mul_right hdm
  · exact fun hdc ↦ hdc.trans hm.1

/-- Positive divisors at most `N`.  This version is defined even at zero and
is convenient for comparing the tested integer with the fixed factor. -/
def positiveDivisorsUpTo (N m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun d ↦ d ∣ m

theorem positiveDivisorsUpTo_eq_of_mem_exactValuationCell
    {N c m : ℕ} (hm : m ∈ exactValuationCell N c) :
    positiveDivisorsUpTo N m = positiveDivisorsUpTo N c := by
  ext d
  simp only [positiveDivisorsUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hdb, hdm⟩
    exact ⟨hdb,
      (dvd_iff_dvd_fixedFactor_of_mem_exactValuationCell
        (by omega) hdb.2 hm).mp hdm⟩
  · rintro ⟨hdb, hdc⟩
    exact ⟨hdb,
      (dvd_iff_dvd_fixedFactor_of_mem_exactValuationCell
        (by omega) hdb.2 hm).mpr hdc⟩

/-- If the target interval lies below the cutoff, its divisor count is
constant throughout an exact valuation cell. -/
theorem divisorCountIoc_eq_of_mem_exactValuationCell
    {N c m y z : ℕ} (hy : 0 < y) (hzN : z ≤ N)
    (hm : m ∈ exactValuationCell N c) :
    divisorCountIoc y z m = divisorCountIoc y z c := by
  unfold divisorCountIoc
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hdyz, hdm⟩
    exact ⟨hdyz,
      (dvd_iff_dvd_fixedFactor_of_mem_exactValuationCell
        (hy.trans hdyz.1) (hdyz.2.trans hzN) hm).mp hdm⟩
  · rintro ⟨hdyz, hdc⟩
    exact ⟨hdyz,
      (dvd_iff_dvd_fixedFactor_of_mem_exactValuationCell
        (hy.trans hdyz.1) (hdyz.2.trans hzN) hm).mpr hdc⟩

end Erdos446
