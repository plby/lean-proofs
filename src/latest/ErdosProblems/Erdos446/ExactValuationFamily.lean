/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.ExactValuationCells

/-!
# Erdős Problem 446: finite families of exact valuation cells

Distinct positive squarefree fixed factors, supported on the primes at most
`N`, determine disjoint exact valuation cells.  Consequently the density of
a finite union is the sum of the individual densities.  Combining this with
the small-divisor rigidity theorem gives an exact finite-family lower bound
for the density of integers having a prescribed divisor multiplicity.
-/

namespace Erdos446

open Filter Finset Set Real
open scoped BigOperators Topology

/-- The union of the exact small-prime valuation cells represented by `C`. -/
def exactValuationFamilyEvent (N : ℕ) (C : Finset ℕ) : Set ℕ :=
  {m | ∃ c ∈ C, m ∈ exactValuationCell N c}

theorem mem_exactValuationFamilyEvent {N : ℕ} {C : Finset ℕ} {m : ℕ} :
    m ∈ exactValuationFamilyEvent N C ↔
      ∃ c ∈ C, m ∈ exactValuationCell N c := by
  rfl

/-- Exact valuation cells belonging to distinct supported squarefree fixed
factors are disjoint. -/
theorem exactValuationCell_pairwiseDisjoint
    {N : ℕ} {C : Finset ℕ}
    (hpos : ∀ c ∈ C, 0 < c)
    (hsq : ∀ c ∈ C, Squarefree c)
    (hcut : ∀ c ∈ C, PrimeFactorsAtMost N c) :
    (C : Set ℕ).PairwiseDisjoint (exactValuationCell N) := by
  intro c hc d hd hcd
  change Disjoint (exactValuationCell N c) (exactValuationCell N d)
  rw [Set.disjoint_left]
  intro m hmc hmd
  have hcPat := primePattern_eq_supportPattern_of_mem_exactValuationCell
    (hpos c hc) (hcut c hc) hmc
  have hdPat := primePattern_eq_supportPattern_of_mem_exactValuationCell
    (hpos d hd) (hcut d hd) hmd
  have hsupport : supportPattern N c = supportPattern N d :=
    hcPat.symm.trans hdPat
  exact hcd (supportPattern_injOn N C hsq hcut hc hd hsupport)

/-- Natural density is additive on two disjoint sets whose densities exist. -/
theorem hasDensity_union_of_disjoint_exactValuation
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

/-- Exact density of a finite disjoint family of squarefree valuation cells. -/
theorem exactValuationFamilyEvent_hasDensity
    {N : ℕ} {C : Finset ℕ}
    (hpos : ∀ c ∈ C, 0 < c)
    (hsq : ∀ c ∈ C, Squarefree c)
    (hcut : ∀ c ∈ C, PrimeFactorsAtMost N c) :
    (exactValuationFamilyEvent N C).HasDensity
      (smallPrimeEulerDensity N * ∑ c ∈ C, 1 / (c : ℝ)) := by
  classical
  induction C using Finset.induction_on with
  | empty =>
      simp [exactValuationFamilyEvent, Set.HasDensity, Set.partialDensity]
  | @insert c C hc ih =>
      have hcpos : 0 < c := hpos c (Finset.mem_insert_self c C)
      have hcsq : Squarefree c := hsq c (Finset.mem_insert_self c C)
      have hccut : PrimeFactorsAtMost N c :=
        hcut c (Finset.mem_insert_self c C)
      have hposC : ∀ d ∈ C, 0 < d := fun d hd ↦
        hpos d (Finset.mem_insert_of_mem hd)
      have hsqC : ∀ d ∈ C, Squarefree d := fun d hd ↦
        hsq d (Finset.mem_insert_of_mem hd)
      have hcutC : ∀ d ∈ C, PrimeFactorsAtMost N d := fun d hd ↦
        hcut d (Finset.mem_insert_of_mem hd)
      have hcell := exactValuationCell_hasDensity N c hcpos
      have hrest := ih hposC hsqC hcutC
      have hpair := exactValuationCell_pairwiseDisjoint
        (N := N) (C := insert c C) hpos hsq hcut
      have hdisj : Disjoint (exactValuationCell N c)
          (exactValuationFamilyEvent N C) := by
        rw [Set.disjoint_left]
        intro m hmc hmC
        rcases hmC with ⟨d, hdC, hmd⟩
        exact Set.disjoint_left.mp
          (hpair (Finset.mem_insert_self c C)
            (Finset.mem_insert_of_mem hdC) (by
              intro hcd
              subst d
              exact hc hdC)) hmc hmd
      have hunion := hasDensity_union_of_disjoint_exactValuation
        hcell hrest hdisj
      have hset : exactValuationFamilyEvent N (insert c C) =
          exactValuationCell N c ∪ exactValuationFamilyEvent N C := by
        ext m
        simp [exactValuationFamilyEvent]
      rw [hset]
      convert hunion using 1
      rw [Finset.sum_insert hc]
      ring

/-- Every member of the finite family has the same target-interval divisor
count throughout its exact valuation cell. -/
theorem exactValuationFamilyEvent_subset_exactDivisorSetIoc
    {N r y z : ℕ} {C : Finset ℕ}
    (hy : 0 < y) (hzN : z ≤ N)
    (hcount : ∀ c ∈ C, divisorCountIoc y z c = r) :
    exactValuationFamilyEvent N C ⊆ exactDivisorSetIoc r y z := by
  intro m hm
  rcases hm with ⟨c, hc, hmc⟩
  change divisorCountIoc y z m = r
  exact (divisorCountIoc_eq_of_mem_exactValuationCell hy hzN hmc).trans
    (hcount c hc)

/-- Exact finite-family lower bound for a prescribed multiplicity.  This is
the fixed-`r` analogue of `squarefree_family_lower_bound`, with exponent-one
conditions included at the selected small primes. -/
theorem exactMultiplicity_squarefree_family_lower_bound
    {N r y z : ℕ} {C : Finset ℕ} (hy : 0 < y) (hzN : z ≤ N)
    (hpos : ∀ c ∈ C, 0 < c)
    (hsq : ∀ c ∈ C, Squarefree c)
    (hcut : ∀ c ∈ C, PrimeFactorsAtMost N c)
    (hcount : ∀ c ∈ C, divisorCountIoc y z c = r) :
    smallPrimeEulerDensity N * (∑ c ∈ C, 1 / (c : ℝ)) ≤
      epsilonR r y z := by
  exact density_le_of_subset
    (exactValuationFamilyEvent_hasDensity hpos hsq hcut)
    (exactDivisorSetIoc_hasDensity r y z hy)
    (exactValuationFamilyEvent_subset_exactDivisorSetIoc hy hzN hcount)

end Erdos446
