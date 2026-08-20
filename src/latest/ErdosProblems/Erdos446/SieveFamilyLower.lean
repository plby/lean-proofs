/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SieveDensity

/-!
# Erdős Problem 446: the finite squarefree sieve family

This module turns the exact finite CRT model into a lower bound for Ford's
divisor density.  Each positive squarefree integer whose prime factors are
below the cutoff determines one exact small-prime pattern.  Distinct integers
give distinct patterns, and the probability of each pattern is at least the
small-prime Euler product divided by the integer.
-/

namespace Erdos446

open Filter Finset Set MeasureTheory Real
open scoped BigOperators Topology

/-- Every prime factor of `c` is at most `N`. -/
def PrimeFactorsAtMost (N c : ℕ) : Prop :=
  ∀ p ∈ c.primeFactors, p ≤ N

/-- The small-prime support belonging to `c`. -/
def supportPattern (N c : ℕ) : Finset (PrimeIndex N) :=
  Finset.univ.filter fun p ↦ p.1 ∈ c.primeFactors

theorem mem_supportPattern_iff {N c : ℕ} {p : PrimeIndex N} :
    p ∈ supportPattern N c ↔ p.1 ∈ c.primeFactors := by
  simp [supportPattern]

private theorem prime_mem_primesUpTo {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) :
    p ∈ primesUpTo N := by
  rw [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hp.two_le, hpN⟩, hp⟩

/-- An exact small-prime pattern equal to the support of a positive squarefree
`c` forces `c` to divide the tested integer. -/
theorem dvd_of_primePattern_eq_supportPattern {N c m : ℕ}
    (hc : Squarefree c) (hcut : PrimeFactorsAtMost N c)
    (hpat : primePattern N m = supportPattern N c) :
    c ∣ m := by
  rw [← Nat.prod_primeFactors_of_squarefree hc]
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes
        (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  · intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    let pN : PrimeIndex N := ⟨p, prime_mem_primesUpTo hpPrime (hcut p hp)⟩
    have hpSupport : pN ∈ supportPattern N c := by
      exact mem_supportPattern_iff.mpr hp
    have hpPattern : pN ∈ primePattern N m := by
      rw [hpat]
      exact hpSupport
    exact mem_primePattern_iff.mp hpPattern

/-- The support map is injective on positive squarefree integers with all
prime factors below the cutoff. -/
theorem supportPattern_injOn (N : ℕ) (C : Finset ℕ)
    (hsq : ∀ c ∈ C, Squarefree c)
    (hcut : ∀ c ∈ C, PrimeFactorsAtMost N c) :
    Set.InjOn (supportPattern N) C := by
  intro c hc d hd hsupport
  have hpf : c.primeFactors = d.primeFactors := by
    ext p
    constructor
    · intro hpc
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpc
      let pN : PrimeIndex N :=
        ⟨p, prime_mem_primesUpTo hpPrime (hcut c hc p hpc)⟩
      have : pN ∈ supportPattern N c := mem_supportPattern_iff.mpr hpc
      rw [hsupport, mem_supportPattern_iff] at this
      exact this
    · intro hpd
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpd
      let pN : PrimeIndex N :=
        ⟨p, prime_mem_primesUpTo hpPrime (hcut d hd p hpd)⟩
      have : pN ∈ supportPattern N d := mem_supportPattern_iff.mpr hpd
      rw [← hsupport, mem_supportPattern_iff] at this
      exact this
  calc
    c = ∏ p ∈ c.primeFactors, p := (Nat.prod_primeFactors_of_squarefree (hsq c hc)).symm
    _ = ∏ p ∈ d.primeFactors, p := by rw [hpf]
    _ = d := Nat.prod_primeFactors_of_squarefree (hsq d hd)

/-- Natural density is monotone when both limiting densities exist. -/
theorem density_le_of_subset {S T : Set ℕ} {a b : ℝ}
    (hS : S.HasDensity a) (hT : T.HasDensity b) (hsub : S ⊆ T) :
    a ≤ b := by
  rw [← sub_nonneg]
  apply ge_of_tendsto (hT.sub hS)
  exact Eventually.of_forall fun n ↦ by
    simp only [sub_nonneg]
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Set.ncard_le_ncard
      (Set.inter_subset_inter_left (Set.Iio n) hsub)

/-- The product of reciprocal primes in the support of a squarefree integer
is its reciprocal. -/
theorem prod_supportPattern_reciprocal {N c : ℕ}
    (hc : Squarefree c) (hcut : PrimeFactorsAtMost N c) :
    (∏ p ∈ supportPattern N c, (p.1 : ℝ)⁻¹) = (c : ℝ)⁻¹ := by
  rw [Finset.prod_inv_distrib]
  congr 1
  have hprod :
      (∏ p ∈ supportPattern N c, (p.1 : ℝ)) =
        ∏ p ∈ c.primeFactors, (p : ℝ) := by
    apply Finset.prod_bij (fun p _ ↦ p.1)
    · intro p hp
      exact mem_supportPattern_iff.mp hp
    · intro p hp q hq hpq
      exact Subtype.ext hpq
    · intro p hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      let pN : PrimeIndex N :=
        ⟨p, prime_mem_primesUpTo hpPrime (hcut p hp)⟩
      exact ⟨pN, mem_supportPattern_iff.mpr hp, rfl⟩
    · intro p hp
      rfl
  rw [hprod]
  simpa using congrArg (fun n : ℕ ↦ (n : ℝ))
    (Nat.prod_primeFactors_of_squarefree hc)

/-- A Bernoulli exact-pattern weight is at least the full Euler product times
the product of the selected reciprocal primes. -/
theorem smallPrimeEulerDensity_mul_selected_le
    (N : ℕ) (T : Finset (PrimeIndex N)) :
    smallPrimeEulerDensity N * (∏ p ∈ T, (p.1 : ℝ)⁻¹) ≤
      primePatternWeight N T := by
  let q : PrimeIndex N → ℝ := fun p ↦ (p.1 : ℝ)⁻¹
  have hs : (primesUpTo N).attach =
      (Finset.univ : Finset (PrimeIndex N)) := by
    ext p
    simp
  have hq0 (p : PrimeIndex N) : 0 ≤ q p := by
    exact inv_nonneg.mpr (by exact_mod_cast (Nat.zero_le p.1))
  have hq1 (p : PrimeIndex N) : q p ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by
      exact_mod_cast (Nat.succ_le_of_lt (primeIndex_pos p)))
  have hcomp0 : 0 ≤ ∏ p ∈ (Finset.univ : Finset (PrimeIndex N)) \ T,
      (1 - q p) := by
    apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (hq1 p)
  have hselected :
      (∏ p ∈ T, (1 - q p) * q p) ≤ ∏ p ∈ T, q p := by
    apply Finset.prod_le_prod
    · intro p hp
      exact mul_nonneg (sub_nonneg.mpr (hq1 p)) (hq0 p)
    · intro p hp
      nlinarith [hq0 p, hq1 p]
  have heuler :
      smallPrimeEulerDensity N =
        (∏ p ∈ (Finset.univ : Finset (PrimeIndex N)) \ T, (1 - q p)) *
          ∏ p ∈ T, (1 - q p) := by
    have hsdiff := Finset.prod_sdiff
      (f := fun p : PrimeIndex N ↦ 1 - q p)
      (show T ⊆ (Finset.univ : Finset (PrimeIndex N)) from Finset.subset_univ T)
    rw [smallPrimeEulerDensity]
    simpa [q, one_div] using hsdiff.symm
  unfold primePatternWeight Erdos697.Bernoulli.weight
  rw [hs, heuler]
  simp only [one_div]
  change
    ((∏ p ∈ (Finset.univ : Finset (PrimeIndex N)) \ T, (1 - q p)) *
        ∏ p ∈ T, (1 - q p)) * (∏ p ∈ T, q p) ≤
      (∏ p ∈ T, q p) *
        ∏ p ∈ (Finset.univ : Finset (PrimeIndex N)) \ T, (1 - q p)
  calc
    ((∏ p ∈ (Finset.univ : Finset (PrimeIndex N)) \ T, (1 - q p)) *
        ∏ p ∈ T, (1 - q p)) * (∏ p ∈ T, q p) =
        (∏ p ∈ (Finset.univ : Finset (PrimeIndex N)) \ T, (1 - q p)) *
          ((∏ p ∈ T, (1 - q p)) * ∏ p ∈ T, q p) := by ring
    _ = (∏ p ∈ (Finset.univ : Finset (PrimeIndex N)) \ T, (1 - q p)) *
          ∏ p ∈ T, ((1 - q p) * q p) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ (∏ p ∈ (Finset.univ : Finset (PrimeIndex N)) \ T, (1 - q p)) *
          ∏ p ∈ T, q p := mul_le_mul_of_nonneg_left hselected hcomp0
    _ = (∏ p ∈ T, q p) *
          ∏ p ∈ (Finset.univ : Finset (PrimeIndex N)) \ T, (1 - q p) := by ring

/-- Pointwise lower bound for the exact pattern belonging to a squarefree
integer. -/
theorem smallPrimeEulerDensity_div_le_patternWeight {N c : ℕ}
    (hc : Squarefree c) (hcut : PrimeFactorsAtMost N c) :
    smallPrimeEulerDensity N / (c : ℝ) ≤
      primePatternWeight N (supportPattern N c) := by
  rw [div_eq_mul_inv, ← prod_supportPattern_reciprocal hc hcut]
  exact smallPrimeEulerDensity_mul_selected_le N (supportPattern N c)

/-- Integers whose exact small-prime support is represented by `C`. -/
def squarefreePatternEvent (N : ℕ) (C : Finset ℕ) : Set ℕ :=
  {m | primePattern N m ∈ C.image (supportPattern N)}

/-- Exact density of the union of the prime-pattern cells represented by
`C`.  No squarefreeness is needed for this identity. -/
theorem squarefreePatternEvent_hasDensity (N : ℕ) (C : Finset ℕ) :
    (squarefreePatternEvent N C).HasDensity
      (∑ T ∈ C.image (supportPattern N), primePatternWeight N T) := by
  have h := primePattern_event_hasDensity N
    (fun T ↦ T ∈ C.image (supportPattern N))
  have hfilter :
      (Finset.univ : Finset (Finset (PrimeIndex N))).filter
          (fun T ↦ T ∈ C.image (supportPattern N)) =
        C.image (supportPattern N) := by
    ext T
    simp
  rw [hfilter] at h
  exact h

/-- If every member of the pattern family lies in `(y,z]`, then its pattern
event is contained in the divisor event. -/
theorem squarefreePatternEvent_subset_divisorSetIoc
    {N y z : ℕ} {C : Finset ℕ}
    (hsq : ∀ c ∈ C, Squarefree c)
    (hcut : ∀ c ∈ C, PrimeFactorsAtMost N c)
    (hinterval : ∀ c ∈ C, c ∈ Finset.Ioc y z) :
    squarefreePatternEvent N C ⊆ divisorSetIoc y z := by
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨c, hc, hpat⟩
  have hdiv : c ∣ m :=
    dvd_of_primePattern_eq_supportPattern (hsq c hc) (hcut c hc) hpat.symm
  rw [divisorSetIoc, Set.mem_setOf_eq, divisorCountIoc]
  exact Finset.card_pos.mpr
    ⟨c, Finset.mem_filter.mpr ⟨hinterval c hc, hdiv⟩⟩

/-- The finite squarefree-family lower bound.  This is the exact CRT sieve
inequality used in Ford's construction. -/
theorem squarefree_family_lower_bound
    {N y z : ℕ} {C : Finset ℕ} (hy : 0 < y)
    (hsq : ∀ c ∈ C, Squarefree c)
    (hcut : ∀ c ∈ C, PrimeFactorsAtMost N c)
    (hinterval : ∀ c ∈ C, c ∈ Finset.Ioc y z) :
    smallPrimeEulerDensity N * (∑ c ∈ C, 1 / (c : ℝ)) ≤ epsilon y z := by
  have hinj := supportPattern_injOn N C hsq hcut
  have hevent := squarefreePatternEvent_hasDensity N C
  have hdivDensity := divisorSetIoc_hasDensity y z hy
  have hmono :
      (∑ T ∈ C.image (supportPattern N), primePatternWeight N T) ≤
        epsilon y z :=
    density_le_of_subset hevent hdivDensity
      (squarefreePatternEvent_subset_divisorSetIoc hsq hcut hinterval)
  calc
    smallPrimeEulerDensity N * (∑ c ∈ C, 1 / (c : ℝ)) =
        ∑ c ∈ C, smallPrimeEulerDensity N / (c : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ ≤ ∑ c ∈ C, primePatternWeight N (supportPattern N c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact smallPrimeEulerDensity_div_le_patternWeight (hsq c hc) (hcut c hc)
    _ = ∑ T ∈ C.image (supportPattern N), primePatternWeight N T := by
      exact (Finset.sum_image hinj).symm
    _ ≤ epsilon y z := hmono

/-- Flexible squarefree-family lower bound.  The exact prime support `c` may
be larger than `z`; it suffices that `c` contain a divisor in `(y,z]`.  This
is the formulation used for `c = a*p` in Ford's lower construction. -/
theorem squarefree_moduli_lower_bound
    {N y z : ℕ} {C : Finset ℕ} (hy : 0 < y)
    (hsq : ∀ c ∈ C, Squarefree c)
    (hcut : ∀ c ∈ C, PrimeFactorsAtMost N c)
    (hwitness : ∀ c ∈ C, ∃ d ∈ Finset.Ioc y z, d ∣ c) :
    smallPrimeEulerDensity N * (∑ c ∈ C, 1 / (c : ℝ)) ≤ epsilon y z := by
  have hinj := supportPattern_injOn N C hsq hcut
  have hevent := squarefreePatternEvent_hasDensity N C
  have hdivDensity := divisorSetIoc_hasDensity y z hy
  have hsub : squarefreePatternEvent N C ⊆ divisorSetIoc y z := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨c, hc, hpat⟩
    have hcm : c ∣ m :=
      dvd_of_primePattern_eq_supportPattern (hsq c hc) (hcut c hc) hpat.symm
    obtain ⟨d, hdIoc, hdc⟩ := hwitness c hc
    rw [divisorSetIoc, Set.mem_setOf_eq, divisorCountIoc]
    exact Finset.card_pos.mpr
      ⟨d, Finset.mem_filter.mpr ⟨hdIoc, hdc.trans hcm⟩⟩
  have hmono :
      (∑ T ∈ C.image (supportPattern N), primePatternWeight N T) ≤
        epsilon y z := density_le_of_subset hevent hdivDensity hsub
  calc
    smallPrimeEulerDensity N * (∑ c ∈ C, 1 / (c : ℝ)) =
        ∑ c ∈ C, smallPrimeEulerDensity N / (c : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ ≤ ∑ c ∈ C, primePatternWeight N (supportPattern N c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact smallPrimeEulerDensity_div_le_patternWeight (hsq c hc) (hcut c hc)
    _ = ∑ T ∈ C.image (supportPattern N), primePatternWeight N T := by
      exact (Finset.sum_image hinj).symm
    _ ≤ epsilon y z := hmono

end Erdos446
