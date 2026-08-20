/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.EulerEstimate
import ErdosProblems.Erdos446.SieveFamilyLower

/-!
# Erdős Problem 446: exact-multiplicity gcd cells

Let `L = lcm(1,…,z)`.  On the residue cell `gcd(L,m)=c`, divisibility of
`m` by every integer at most `z` is exactly divisibility by `c`.  Thus a
finite family of moduli `c` having exactly `r` divisors in `(y,z]` gives a
disjoint family of residue cells inside the exact-`r` event.

This avoids a possible source of spurious divisors in a squarefree
prime-support sieve: prime support controls whether `p` divides an integer,
whereas the gcd cell controls every prime power up to `z`.
-/

namespace Erdos446

open Filter Finset Set Real
open scoped BigOperators Topology

/-- The residue cell on which the gcd with `lcm(1,…,z)` is exactly `c`. -/
def lcmGcdCell (z c : ℕ) : Set ℕ :=
  {m | (Nat.lcmUpto z).gcd m = c}

/-- A finite disjoint union of exact gcd cells. -/
def lcmGcdCellFamily (z : ℕ) (C : Finset ℕ) : Set ℕ :=
  {m | (Nat.lcmUpto z).gcd m ∈ C}

/-- Gcd representatives whose divisor count in `(y,z]` is exactly `r`. -/
def exactGcdRepresentatives (r y z : ℕ) : Finset ℕ :=
  (Nat.lcmUpto z).divisors.filter fun c ↦ divisorCountIoc y z c = r

/-- Gcd representatives having at least one divisor in `(y,z]`. -/
def positiveGcdRepresentatives (y z : ℕ) : Finset ℕ :=
  (Nat.lcmUpto z).divisors.filter fun c ↦ 0 < divisorCountIoc y z c

theorem lcmUpto_dvd_of_pos_le {d z : ℕ} (hd : 0 < d) (hdz : d ≤ z) :
    d ∣ Nat.lcmUpto z := by
  rw [Nat.lcmUpto]
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hd, hdz⟩)

/-- Taking the gcd with `lcm(1,…,z)` preserves every divisor in `(y,z]`. -/
theorem divisorCountIoc_gcd_lcmUpto (y z m : ℕ) :
    divisorCountIoc y z ((Nat.lcmUpto z).gcd m) =
      divisorCountIoc y z m := by
  unfold divisorCountIoc
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hdIoc, hdgcd⟩
    exact ⟨hdIoc, hdgcd.trans (Nat.gcd_dvd_right _ _)⟩
  · rintro ⟨hdIoc, hdm⟩
    have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le y) (Finset.mem_Ioc.mp hdIoc).1
    have hdz : d ≤ z := (Finset.mem_Ioc.mp hdIoc).2
    exact ⟨hdIoc, Nat.dvd_gcd (lcmUpto_dvd_of_pos_le hdpos hdz) hdm⟩

theorem lcmGcdCell_periodic (z c : ℕ) :
    Function.Periodic (fun m ↦ m ∈ lcmGcdCell z c) (Nat.lcmUpto z) := by
  intro m
  simp [lcmGcdCell]

/-- Exact density of one gcd cell. -/
theorem lcmGcdCell_hasDensity {z c : ℕ} (hc : c ∣ Nat.lcmUpto z) :
    (lcmGcdCell z c).HasDensity
      ((Nat.totient (Nat.lcmUpto z / c) : ℝ) / (Nat.lcmUpto z : ℝ)) := by
  have h := hasDensity_of_periodic
    (fun m ↦ (Nat.lcmUpto z).gcd m = c)
    (Nat.lcmUpto z) (Nat.lcmUpto_pos z) (lcmGcdCell_periodic z c)
  rw [Nat.totient_div_of_dvd hc]
  simpa [lcmGcdCell] using h

private theorem gcdFibers_pairwiseDisjoint (z : ℕ) (C : Finset ℕ) :
    (C : Set ℕ).PairwiseDisjoint
      (fun c ↦ (Finset.range (Nat.lcmUpto z)).filter
        (fun m ↦ (Nat.lcmUpto z).gcd m = c)) := by
  intro c hc d hd hcd
  change Disjoint
    ((Finset.range (Nat.lcmUpto z)).filter
      (fun m ↦ (Nat.lcmUpto z).gcd m = c))
    ((Finset.range (Nat.lcmUpto z)).filter
      (fun m ↦ (Nat.lcmUpto z).gcd m = d))
  rw [Finset.disjoint_left]
  intro m hmc hmd
  simp only [Finset.mem_filter] at hmc hmd
  exact hcd (hmc.2.symm.trans hmd.2)

/-- Exact density of a finite union of gcd cells. -/
theorem lcmGcdCellFamily_hasDensity
    {z : ℕ} {C : Finset ℕ} (hC : ∀ c ∈ C, c ∣ Nat.lcmUpto z) :
    (lcmGcdCellFamily z C).HasDensity
      ((∑ c ∈ C, (Nat.totient (Nat.lcmUpto z / c) : ℝ)) /
        (Nat.lcmUpto z : ℝ)) := by
  have hperiodic : Function.Periodic
      (fun m ↦ (Nat.lcmUpto z).gcd m ∈ C) (Nat.lcmUpto z) := by
    intro m
    simp
  have h := hasDensity_of_periodic
    (fun m ↦ (Nat.lcmUpto z).gcd m ∈ C)
    (Nat.lcmUpto z) (Nat.lcmUpto_pos z) hperiodic
  have hfilter :
      (Finset.range (Nat.lcmUpto z)).filter
          (fun m ↦ (Nat.lcmUpto z).gcd m ∈ C) =
        C.biUnion (fun c ↦ (Finset.range (Nat.lcmUpto z)).filter
          (fun m ↦ (Nat.lcmUpto z).gcd m = c)) := by
    ext m
    simp [and_comm]
  have hcard :
      ((Finset.range (Nat.lcmUpto z)).filter
          (fun m ↦ (Nat.lcmUpto z).gcd m ∈ C)).card =
        ∑ c ∈ C, Nat.totient (Nat.lcmUpto z / c) := by
    rw [hfilter, Finset.card_biUnion (gcdFibers_pairwiseDisjoint z C)]
    apply Finset.sum_congr rfl
    intro c hc
    exact (Nat.totient_div_of_dvd (hC c hc)).symm
  rw [hcard] at h
  simpa [lcmGcdCellFamily] using h

/-- The small-prime Euler product is the normalized totient of the universal
lcm. -/
theorem smallPrimeEulerDensity_eq_totient_lcmUpto_div (z : ℕ) :
    smallPrimeEulerDensity z =
      (Nat.totient (Nat.lcmUpto z) : ℝ) / (Nat.lcmUpto z : ℝ) := by
  have heuler : smallPrimeEulerDensity z =
      ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ)) := by
    rw [smallPrimeEulerDensity]
    apply Finset.prod_bij (fun p _ ↦ p.1)
    · intro p hp
      rw [Nat.mem_primesLE]
      have hp' := Finset.mem_filter.mp p.2
      exact ⟨(Finset.mem_Icc.mp hp'.1).2, hp'.2⟩
    · intro p hp q hq hpq
      exact Subtype.ext hpq
    · intro p hp
      have hp' := Nat.mem_primesLE.mp hp
      let pz : PrimeIndex z := ⟨p, by
        rw [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hp'.2.two_le, hp'.1⟩, hp'.2⟩⟩
      exact ⟨pz, Finset.mem_univ _, rfl⟩
    · intro p hp
      rfl
  have htotQ := Nat.totient_eq_mul_prod_factors (Nat.lcmUpto z)
  have htotR : (Nat.totient (Nat.lcmUpto z) : ℝ) =
      (Nat.lcmUpto z : ℝ) *
        ∏ p ∈ (Nat.lcmUpto z).primeFactors,
          (1 - 1 / (p : ℝ)) := by
    have hcast := congrArg (fun q : ℚ ↦ (q : ℝ)) htotQ
    simpa using hcast
  rw [heuler, ← Nat.primeFactors_lcmUpto]
  rw [htotR]
  field_simp [Nat.cast_ne_zero.mpr (Nat.lcmUpto_ne_zero z)]

/-- The normalized totient is antitone under divisibility. -/
theorem totient_div_self_anti_of_dvd
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) :
    (Nat.totient b : ℝ) / (b : ℝ) ≤
      (Nat.totient a : ℝ) / (a : ℝ) := by
  have hratio (n : ℕ) (hn : 0 < n) :
      (Nat.totient n : ℝ) / (n : ℝ) =
        ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
    have htotQ := Nat.totient_eq_mul_prod_factors n
    have htotR : (Nat.totient n : ℝ) = (n : ℝ) *
        ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
      have hcast := congrArg (fun q : ℚ ↦ (q : ℝ)) htotQ
      simpa using hcast
    rw [htotR]
    field_simp [Nat.cast_ne_zero.mpr hn.ne']
  rw [hratio b hb, hratio a ha]
  have hsub : a.primeFactors ⊆ b.primeFactors :=
    Nat.primeFactors_mono hab hb.ne'
  apply Finset.prod_le_prod_of_subset_of_le_one hsub
  · intro p hpb
    have hp := Nat.prime_of_mem_primeFactors hpb
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    exact sub_nonneg.mpr (by
      rw [one_div]
      exact inv_le_one_of_one_le₀ hp1)
  · intro p hpb hpa
    exact sub_le_self 1 (by positivity : 0 ≤ 1 / (p : ℝ))

/-- Each exact gcd cell has at least the universal Euler density divided by
its gcd representative. -/
theorem smallPrimeEulerDensity_div_le_gcdCellDensity
    {z c : ℕ} (hc : c ∣ Nat.lcmUpto z) :
    smallPrimeEulerDensity z / (c : ℝ) ≤
      (Nat.totient (Nat.lcmUpto z / c) : ℝ) /
        (Nat.lcmUpto z : ℝ) := by
  have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hc (Nat.lcmUpto_pos z)
  have hqpos : 0 < Nat.lcmUpto z / c :=
    Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos z) hc) hcpos
  have hratio := totient_div_self_anti_of_dvd hqpos
    (Nat.lcmUpto_pos z) (Nat.div_dvd_of_dvd hc)
  rw [← smallPrimeEulerDensity_eq_totient_lcmUpto_div] at hratio
  calc
    smallPrimeEulerDensity z / (c : ℝ) ≤
        ((Nat.totient (Nat.lcmUpto z / c) : ℝ) /
          ((Nat.lcmUpto z / c : ℕ) : ℝ)) / (c : ℝ) :=
      by
        have hmul := mul_le_mul_of_nonneg_right hratio
          (inv_nonneg.mpr (Nat.cast_nonneg c))
        simpa only [div_eq_mul_inv] using hmul
    _ = (Nat.totient (Nat.lcmUpto z / c) : ℝ) /
        (Nat.lcmUpto z : ℝ) := by
      rw [div_div]
      rw [← Nat.cast_mul, Nat.div_mul_cancel hc]

/-- A squarefree number supported on primes at most `z` divides the
universal lcm. -/
theorem dvd_lcmUpto_of_squarefree_of_primeFactorsAtMost
    {z c : ℕ} (hc : Squarefree c) (hcut : PrimeFactorsAtMost z c) :
    c ∣ Nat.lcmUpto z := by
  have hsub : c.primeFactors ⊆ Nat.primesLE z := by
    intro p hp
    rw [Nat.mem_primesLE]
    exact ⟨hcut p hp, Nat.prime_of_mem_primeFactors hp⟩
  have hprod : (∏ p ∈ c.primeFactors, p) ∣ primorial z := by
    rw [primorial_eq_prod_primesLE]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  rw [← Nat.prod_primeFactors_of_squarefree hc]
  exact hprod.trans (Nat.primorial_dvd_lcmUpto z)

/-- Every selected gcd cell lies in the prescribed exact-multiplicity
event when its gcd representative has that multiplicity. -/
theorem lcmGcdCellFamily_subset_exactDivisorSetIoc
    {r y z : ℕ} {C : Finset ℕ}
    (hExact : ∀ c ∈ C, divisorCountIoc y z c = r) :
    lcmGcdCellFamily z C ⊆ exactDivisorSetIoc r y z := by
  intro m hm
  have hcm : divisorCountIoc y z ((Nat.lcmUpto z).gcd m) = r :=
    hExact _ hm
  rw [divisorCountIoc_gcd_lcmUpto] at hcm
  exact hcm

/-- The exact-`r` divisor event is precisely the union of all gcd cells whose
representative has divisor count `r`. -/
theorem lcmGcdCellFamily_exactGcdRepresentatives
    (r y z : ℕ) :
    lcmGcdCellFamily z (exactGcdRepresentatives r y z) =
      exactDivisorSetIoc r y z := by
  ext m
  simp only [lcmGcdCellFamily, exactGcdRepresentatives,
    exactDivisorSetIoc, Set.mem_ofPred_eq, Finset.mem_filter]
  constructor
  · rintro ⟨hcdiv, hcount⟩
    rwa [divisorCountIoc_gcd_lcmUpto] at hcount
  · intro hcount
    refine ⟨?_, ?_⟩
    · rw [Nat.mem_divisors]
      exact ⟨Nat.gcd_dvd_left _ _, Nat.lcmUpto_ne_zero z⟩
    · rwa [divisorCountIoc_gcd_lcmUpto]

/-- Exact finite totient formula for the prescribed-multiplicity density. -/
theorem epsilonR_eq_sum_totient_gcdRepresentatives
    (r y z : ℕ) (hy : 0 < y) :
    epsilonR r y z =
      ((∑ c ∈ exactGcdRepresentatives r y z,
          (Nat.totient (Nat.lcmUpto z / c) : ℝ)) /
        (Nat.lcmUpto z : ℝ)) := by
  have hC : ∀ c ∈ exactGcdRepresentatives r y z,
      c ∣ Nat.lcmUpto z := by
    intro c hc
    exact Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hc).1
  have hfamily := lcmGcdCellFamily_hasDensity hC
  rw [lcmGcdCellFamily_exactGcdRepresentatives] at hfamily
  exact tendsto_nhds_unique (exactDivisorSetIoc_hasDensity r y z hy) hfamily

/-- The union event is likewise exactly the union of the positive-count gcd
cells. -/
theorem lcmGcdCellFamily_positiveGcdRepresentatives
    (y z : ℕ) :
    lcmGcdCellFamily z (positiveGcdRepresentatives y z) =
      divisorSetIoc y z := by
  ext m
  simp only [lcmGcdCellFamily, positiveGcdRepresentatives,
    divisorSetIoc, Set.mem_ofPred_eq, Finset.mem_filter]
  constructor
  · rintro ⟨hcdiv, hcount⟩
    rwa [divisorCountIoc_gcd_lcmUpto] at hcount
  · intro hcount
    refine ⟨?_, ?_⟩
    · rw [Nat.mem_divisors]
      exact ⟨Nat.gcd_dvd_left _ _, Nat.lcmUpto_ne_zero z⟩
    · rwa [divisorCountIoc_gcd_lcmUpto]

/-- Exact finite totient formula for the divisor-union density. -/
theorem epsilon_eq_sum_totient_positiveGcdRepresentatives
    (y z : ℕ) (hy : 0 < y) :
    epsilon y z =
      ((∑ c ∈ positiveGcdRepresentatives y z,
          (Nat.totient (Nat.lcmUpto z / c) : ℝ)) /
        (Nat.lcmUpto z : ℝ)) := by
  have hC : ∀ c ∈ positiveGcdRepresentatives y z,
      c ∣ Nat.lcmUpto z := by
    intro c hc
    exact Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hc).1
  have hfamily := lcmGcdCellFamily_hasDensity hC
  rw [lcmGcdCellFamily_positiveGcdRepresentatives] at hfamily
  exact tendsto_nhds_unique (divisorSetIoc_hasDensity y z hy) hfamily

/-- Exact gcd-cell lower bound before replacing the totient weights by a
uniform Euler factor. -/
theorem exactMultiplicity_gcdCell_lower
    {r y z : ℕ} {C : Finset ℕ} (hy : 0 < y)
    (hC : ∀ c ∈ C, c ∣ Nat.lcmUpto z)
    (hExact : ∀ c ∈ C, divisorCountIoc y z c = r) :
    ((∑ c ∈ C, (Nat.totient (Nat.lcmUpto z / c) : ℝ)) /
        (Nat.lcmUpto z : ℝ)) ≤ epsilonR r y z := by
  exact density_le_of_subset
    (lcmGcdCellFamily_hasDensity hC)
    (exactDivisorSetIoc_hasDensity r y z hy)
    (lcmGcdCellFamily_subset_exactDivisorSetIoc hExact)

/-- Reciprocal-mass form of the exact gcd-cell sieve.  Unlike a prime-support
cell, this statement guarantees *exactly* `r` divisors, including full
control of prime powers. -/
theorem exactMultiplicity_gcdCell_reciprocal_lower
    {r y z : ℕ} {C : Finset ℕ} (hy : 0 < y)
    (hC : ∀ c ∈ C, c ∣ Nat.lcmUpto z)
    (hExact : ∀ c ∈ C, divisorCountIoc y z c = r) :
    smallPrimeEulerDensity z * (∑ c ∈ C, 1 / (c : ℝ)) ≤
      epsilonR r y z := by
  apply le_trans _ (exactMultiplicity_gcdCell_lower hy hC hExact)
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro c hc
  simpa only [mul_one, one_mul, div_eq_mul_inv] using
    (smallPrimeEulerDensity_div_le_gcdCellDensity (hC c hc))

/-- Squarefree-support specialization, directly comparable to the original
finite CRT family lower bound.  The conclusion controls exact multiplicity,
not merely membership in the divisor union. -/
theorem exactMultiplicity_squarefree_gcdCell_lower
    {r y z : ℕ} {C : Finset ℕ} (hy : 0 < y)
    (hsq : ∀ c ∈ C, Squarefree c)
    (hcut : ∀ c ∈ C, PrimeFactorsAtMost z c)
    (hExact : ∀ c ∈ C, divisorCountIoc y z c = r) :
    smallPrimeEulerDensity z * (∑ c ∈ C, 1 / (c : ℝ)) ≤
      epsilonR r y z := by
  apply exactMultiplicity_gcdCell_reciprocal_lower hy _ hExact
  intro c hc
  exact dvd_lcmUpto_of_squarefree_of_primeFactorsAtMost
    (hsq c hc) (hcut c hc)

end Erdos446
