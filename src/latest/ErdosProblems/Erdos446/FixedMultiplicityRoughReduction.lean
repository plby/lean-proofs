/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedRoughSieve

/-!
# Erdős Problem 446: rough-factor reduction for exact multiplicity

This is the exact finite version of the first reduction in Ford's proof.
For a fixed `N`-smooth factor `c`, write `n = c*b`, where `b` is `N`-rough.
Every divisor of `n` not exceeding `N` then already divides `c`.  Hence the
number of divisors in a prescribed interval is exactly the corresponding
number for `c`.  Smooth factors give disjoint rough-factor cells, so their
reciprocal masses add without overcounting.
-/

namespace Erdos446

open Filter Finset Set Real
open scoped BigOperators Topology

/-- A number at most the roughness cutoff is coprime to an `N`-rough number. -/
theorem coprime_roughAt_of_le {N d b : ℕ} (hd : 0 < d) (hdN : d ≤ N)
    (hb : roughAt N b) : d.Coprime b := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd hne
  have hpd : p ∣ d := (Nat.dvd_gcd_iff.mp hpgcd).1
  have hpb : p ∣ b := (Nat.dvd_gcd_iff.mp hpgcd).2
  have hpN : p ≤ N := (Nat.le_of_dvd hd hpd).trans hdN
  have hpCut : p ∈ primesUpTo N := by
    simp [primesUpTo, hp, hp.two_le, hpN]
  exact (roughAt_iff.mp hb p hpCut) hpb

/-- Every `N`-smooth positive number is coprime to an `N`-rough number. -/
theorem coprime_roughAt_of_primeFactorsAtMost {N a b : ℕ}
    (ha : 0 < a) (hcut : PrimeFactorsAtMost N a) (hb : roughAt N b) :
    a.Coprime b := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd hne
  have hpa : p ∣ a := (Nat.dvd_gcd_iff.mp hpgcd).1
  have hpb : p ∣ b := (Nat.dvd_gcd_iff.mp hpgcd).2
  have hpFactors : p ∈ a.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpa, ha.ne'⟩
  have hpCut : p ∈ primesUpTo N := by
    simp [primesUpTo, hp, hp.two_le, hcut p hpFactors]
  exact (roughAt_iff.mp hb p hpCut) hpb

/-- The rough quotient contributes no divisor at or below the cutoff. -/
theorem dvd_fixedFactor_iff_dvd_roughProduct
    {N c b d : ℕ} (hd : 0 < d) (hdN : d ≤ N) (hb : roughAt N b) :
    d ∣ c * b ↔ d ∣ c := by
  constructor
  · exact (coprime_roughAt_of_le hd hdN hb).dvd_of_dvd_mul_right
  · exact fun h ↦ h.mul_right b

/-- Once `n = c*b` with a rough quotient, every divisor in `(y,z]`, for
`z ≤ N`, is already a divisor of `c`. -/
theorem divisorCountIoc_eq_fixedFactor_of_rough
    {N c n y z : ℕ} (hzN : z ≤ N) (hn : n ∈ roughFactorEvent N c) :
    divisorCountIoc y z n = divisorCountIoc y z c := by
  have hfactor : n = c * (n / c) := (Nat.mul_div_cancel' hn.1).symm
  unfold divisorCountIoc
  congr 1
  apply Finset.filter_congr
  intro d hdIoc
  have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le y) (Finset.mem_Ioc.mp hdIoc).1
  have hdN : d ≤ N := (Finset.mem_Ioc.mp hdIoc).2.trans hzN
  rw [hfactor, dvd_fixedFactor_iff_dvd_roughProduct hdpos hdN hn.2]

/-- Distinct smooth factors determine disjoint rough-factor cells.  This is
the uniqueness of the factorization `n = c*b` at the roughness cutoff. -/
theorem roughFactorEvent_disjoint {N c d : ℕ}
    (hc : 0 < c) (hd : 0 < d)
    (hcCut : PrimeFactorsAtMost N c) (hdCut : PrimeFactorsAtMost N d)
    (hcd : c ≠ d) :
    Disjoint (roughFactorEvent N c) (roughFactorEvent N d) := by
  rw [Set.disjoint_left]
  intro n hnc hnd
  have hncFactor : n = c * (n / c) := (Nat.mul_div_cancel' hnc.1).symm
  have hndFactor : n = d * (n / d) := (Nat.mul_div_cancel' hnd.1).symm
  have hcDvdProd : c ∣ d * (n / d) := hndFactor ▸ hnc.1
  have hdDvdProd : d ∣ c * (n / c) := hncFactor ▸ hnd.1
  have hcdvd : c ∣ d :=
    (coprime_roughAt_of_primeFactorsAtMost hc hcCut hnd.2).dvd_of_dvd_mul_right
      hcDvdProd
  have hddvc : d ∣ c :=
    (coprime_roughAt_of_primeFactorsAtMost hd hdCut hnc.2).dvd_of_dvd_mul_right
      hdDvdProd
  exact hcd (Nat.dvd_antisymm hcdvd hddvc)

/-- Union of the rough-factor cells belonging to a finite smooth family. -/
def roughFamilyEvent (N : ℕ) (C : Finset ℕ) : Set ℕ :=
  {n | ∃ c ∈ C, n ∈ roughFactorEvent N c}

instance roughFamilyEventDecidable (N : ℕ) (C : Finset ℕ) (n : ℕ) :
    Decidable (n ∈ roughFamilyEvent N C) := by
  unfold roughFamilyEvent
  infer_instance

theorem roughFamilyEvent_empty (N : ℕ) : roughFamilyEvent N ∅ = ∅ := by
  ext n
  simp [roughFamilyEvent]

theorem roughFamilyEvent_insert (N c : ℕ) (C : Finset ℕ) :
    roughFamilyEvent N (insert c C) =
      roughFactorEvent N c ∪ roughFamilyEvent N C := by
  ext n
  simp [roughFamilyEvent, or_comm, or_left_comm]

/-- Natural densities add over a disjoint union. -/
theorem hasDensity_union_of_disjoint
    {S T : Set ℕ} {s t : ℝ} (hS : S.HasDensity s)
    (hT : T.HasDensity t) (hdisj : Disjoint S T) :
    (S ∪ T).HasDensity (s + t) := by
  rw [Set.HasDensity] at hS hT ⊢
  apply (hS.add hT).congr'
  filter_upwards with n
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  have hST : Disjoint (S ∩ Set.Iio n) (T ∩ Set.Iio n) :=
    hdisj.mono inter_subset_left inter_subset_left
  rw [show (S ∪ T) ∩ Set.Iio n =
      (S ∩ Set.Iio n) ∪ (T ∩ Set.Iio n) by ext; aesop]
  rw [Set.ncard_union_eq hST]
  push_cast
  ring

/-- The exact rough-sieve density for a finite family of smooth factors. -/
theorem roughFamilyEvent_hasDensity (N : ℕ) (C : Finset ℕ)
    (hpos : ∀ c ∈ C, 0 < c)
    (hcut : ∀ c ∈ C, PrimeFactorsAtMost N c) :
    (roughFamilyEvent N C).HasDensity
      (∑ c ∈ C, smallPrimeEulerDensity N / (c : ℝ)) := by
  classical
  induction C using Finset.induction_on with
  | empty =>
      simp [roughFamilyEvent_empty, Set.HasDensity, Set.partialDensity]
  | @insert c C hc ih =>
      have hcpos : 0 < c := hpos c (Finset.mem_insert_self c C)
      have hccut : PrimeFactorsAtMost N c :=
        hcut c (Finset.mem_insert_self c C)
      have hCpos : ∀ d ∈ C, 0 < d := fun d hd ↦
        hpos d (Finset.mem_insert_of_mem hd)
      have hCcut : ∀ d ∈ C, PrimeFactorsAtMost N d := fun d hd ↦
        hcut d (Finset.mem_insert_of_mem hd)
      have hdisj : Disjoint (roughFactorEvent N c) (roughFamilyEvent N C) := by
        rw [Set.disjoint_left]
        intro n hnc hnC
        rcases hnC with ⟨d, hdC, hnd⟩
        have hcd : c ≠ d := fun heq ↦ hc (heq ▸ hdC)
        exact Set.disjoint_left.mp
          (roughFactorEvent_disjoint hcpos (hCpos d hdC) hccut
            (hCcut d hdC) hcd) hnc hnd
      rw [roughFamilyEvent_insert, Finset.sum_insert hc]
      exact hasDensity_union_of_disjoint
        (roughFactorEvent_hasDensity N c hcpos)
        (ih hCpos hCcut) hdisj

/-- Every rough-factor cell in the family has the divisor multiplicity of
its fixed factor. -/
theorem roughFamilyEvent_subset_exactDivisorSetIoc
    {N y z r : ℕ} {C : Finset ℕ} (hzN : z ≤ N)
    (hexact : ∀ c ∈ C, divisorCountIoc y z c = r) :
    roughFamilyEvent N C ⊆ exactDivisorSetIoc r y z := by
  intro n hn
  rcases hn with ⟨c, hc, hnc⟩
  rw [exactDivisorSetIoc, Set.mem_setOf_eq,
    divisorCountIoc_eq_fixedFactor_of_rough hzN hnc]
  exact hexact c hc

/-- Actual finite prefix count of the rough-factor construction. -/
def roughFamilyPrefixCount (N : ℕ) (C : Finset ℕ) (X : ℕ) : ℕ :=
  ((Finset.range X).filter fun n ↦ n ∈ roughFamilyEvent N C).card

/-- The constructed rough-factor prefix injects into the exact-divisor
prefix.  This is the finite-count form preceding passage to density. -/
theorem roughFamilyPrefixCount_le_exactDivisorPrefixCount
    {N y z r X : ℕ} {C : Finset ℕ} (hzN : z ≤ N)
    (hexact : ∀ c ∈ C, divisorCountIoc y z c = r) :
    roughFamilyPrefixCount N C X ≤ exactDivisorPrefixCount r X y z := by
  unfold roughFamilyPrefixCount exactDivisorPrefixCount
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, roughFamilyEvent_subset_exactDivisorSetIoc hzN hexact hn.2⟩

/-- Quantitative complete-period prefix lower bound for one fixed factor.
It is the literal finite version of `n = c*b` with `b` rough. -/
theorem roughFactor_completePeriod_prefix_lower
    {N c y z r : ℕ} (q : ℕ) (hc : 0 < c) (hzN : z ≤ N)
    (hexact : divisorCountIoc y z c = r) :
    q * ((Finset.range (roughPeriod N)).filter (roughAt N)).card ≤
      exactDivisorPrefixCount r (q * (c * roughPeriod N)) y z := by
  have hsub :
      ((Finset.range (q * (c * roughPeriod N))).filter
          (fun n ↦ n ∈ roughFactorEvent N c)) ⊆
        (Finset.range (q * (c * roughPeriod N))).filter
          (fun n ↦ divisorCountIoc y z n = r) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, ?_⟩
    rw [divisorCountIoc_eq_fixedFactor_of_rough hzN hn.2, hexact]
  rw [← card_roughFactorEvent_completePeriods N c q hc]
  exact Finset.card_le_card hsub

/-- Exact-multiplicity form of the initial rough-number reduction.  It is
the density counterpart of Ford's (39), before the reciprocal-prime
interval estimate is inserted. -/
theorem exactMultiplicity_roughFamily_lower
    {N y z r : ℕ} {C : Finset ℕ} (hy : 0 < y) (hzN : z ≤ N)
    (hpos : ∀ c ∈ C, 0 < c)
    (hcut : ∀ c ∈ C, PrimeFactorsAtMost N c)
    (hexact : ∀ c ∈ C, divisorCountIoc y z c = r) :
    smallPrimeEulerDensity N * (∑ c ∈ C, 1 / (c : ℝ)) ≤
      epsilonR r y z := by
  have hfamily := roughFamilyEvent_hasDensity N C hpos hcut
  have hexactDensity := exactDivisorSetIoc_hasDensity r y z hy
  have hle := density_le_of_subset hfamily hexactDensity
    (roughFamilyEvent_subset_exactDivisorSetIoc hzN hexact)
  calc
    smallPrimeEulerDensity N * (∑ c ∈ C, 1 / (c : ℝ)) =
        ∑ c ∈ C, smallPrimeEulerDensity N / (c : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ ≤ epsilonR r y z := hle

end Erdos446
