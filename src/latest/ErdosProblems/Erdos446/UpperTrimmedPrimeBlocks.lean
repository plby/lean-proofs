/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.WeightedTrimmingBridge
import ErdosProblems.Erdos446.UpperBlockMassError

/-!
# Erdős Problem 446: one-sided prime blocks

The fixed doubly-exponential prime blocks have reciprocal mass
`log 2 + O(2⁻ʲ)`, with errors of either sign.  For the upper bound we retain a
maximal subblock of mass at most `log 2`.  A general finite maximality lemma
shows that the discarded mass is at most the positive excess plus one atom;
hence the discarded masses form a geometrically summable residual pool.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

def cappedSubsets (S : Finset ℕ) (wt : ℕ → ℝ) (L : ℝ) :
    Finset (Finset ℕ) :=
  S.powerset.filter fun T ↦ (∑ x ∈ T, wt x) ≤ L

theorem cappedSubsets_nonempty
    (S : Finset ℕ) (wt : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (cappedSubsets S wt L).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [cappedSubsets, hL]

theorem exists_max_card_cappedSubset
    (S : Finset ℕ) (wt : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ T ∈ cappedSubsets S wt L,
      ∀ U ∈ cappedSubsets S wt L, U.card ≤ T.card :=
  Finset.exists_max_image (cappedSubsets S wt L) Finset.card
    (cappedSubsets_nonempty S wt hL)

/-- A maximum-cardinality subset of `S` whose total weight is at most `L`. -/
noncomputable def maximalCappedSubset
    (S : Finset ℕ) (wt : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) : Finset ℕ :=
  Classical.choose (exists_max_card_cappedSubset S wt hL)

theorem maximalCappedSubset_mem
    (S : Finset ℕ) (wt : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    maximalCappedSubset S wt L hL ∈ cappedSubsets S wt L :=
  (Classical.choose_spec (exists_max_card_cappedSubset S wt hL)).1

theorem card_le_maximalCappedSubset
    (S : Finset ℕ) (wt : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    {U : Finset ℕ} (hU : U ∈ cappedSubsets S wt L) :
    U.card ≤ (maximalCappedSubset S wt L hL).card :=
  (Classical.choose_spec (exists_max_card_cappedSubset S wt hL)).2 U hU

theorem maximalCappedSubset_subset
    (S : Finset ℕ) (wt : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    maximalCappedSubset S wt L hL ⊆ S := by
  have hm := maximalCappedSubset_mem S wt L hL
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hm).1

theorem maximalCappedSubset_weight_le
    (S : Finset ℕ) (wt : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    (∑ x ∈ maximalCappedSubset S wt L hL, wt x) ≤ L := by
  exact (Finset.mem_filter.mp
    (maximalCappedSubset_mem S wt L hL)).2

/-- Adding any omitted element to a maximum-cardinality capped subset crosses
the cap. -/
theorem lt_weight_insert_maximalCappedSubset
    (S : Finset ℕ) (wt : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    {x : ℕ} (hxS : x ∈ S)
    (hxT : x ∉ maximalCappedSubset S wt L hL) :
    L < ∑ y ∈ insert x (maximalCappedSubset S wt L hL), wt y := by
  by_contra hnot
  have hle : (∑ y ∈ insert x (maximalCappedSubset S wt L hL), wt y) ≤ L :=
    le_of_not_gt hnot
  have hmem : insert x (maximalCappedSubset S wt L hL) ∈
      cappedSubsets S wt L := by
    rw [cappedSubsets, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset hxS
      (maximalCappedSubset_subset S wt L hL), hle⟩
  have hcard := card_le_maximalCappedSubset S wt L hL hmem
  rw [Finset.card_insert_of_notMem hxT] at hcard
  omega

/-- The discarded weight is bounded by the excess above the cap plus one
largest atom. -/
theorem residual_weight_maximalCappedSubset_le
    (S : Finset ℕ) (wt : ℕ → ℝ) (L E A : ℝ) (hL : 0 ≤ L)
    (hE : 0 ≤ E) (hA : 0 ≤ A)
    (htotal : (∑ x ∈ S, wt x) ≤ L + E)
    (hatom : ∀ x ∈ S, wt x ≤ A) :
    (∑ x ∈ S \ maximalCappedSubset S wt L hL, wt x) ≤ E + A := by
  let T := maximalCappedSubset S wt L hL
  by_cases hres : (S \ T).Nonempty
  · obtain ⟨x, hx⟩ := hres
    have hxS : x ∈ S := (Finset.mem_sdiff.mp hx).1
    have hxT : x ∉ T := (Finset.mem_sdiff.mp hx).2
    have hcross := lt_weight_insert_maximalCappedSubset
      S wt L hL hxS hxT
    rw [Finset.sum_insert hxT] at hcross
    have hTsub : T ⊆ S := maximalCappedSubset_subset S wt L hL
    have hsplit : (∑ y ∈ T, wt y) + (∑ y ∈ S \ T, wt y) =
        ∑ y ∈ S, wt y := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff),
        Finset.union_sdiff_of_subset hTsub]
    have hxA := hatom x hxS
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hres]
    simp
    exact add_nonneg hE hA

/-- The retained part of the `j`th prime block. -/
noncomputable def retainedPrimeBlock (j : ℕ) : Finset ℕ :=
  maximalCappedSubset (primeBlock j) (fun p ↦ 1 / (p : ℝ))
    (Real.log 2) (Real.log_pos one_lt_two).le

/-- The geometrically small discarded part of the `j`th prime block. -/
noncomputable def residualPrimeBlock (j : ℕ) : Finset ℕ :=
  primeBlock j \ retainedPrimeBlock j

theorem retainedPrimeBlock_subset (j : ℕ) :
    retainedPrimeBlock j ⊆ primeBlock j :=
  maximalCappedSubset_subset _ _ _ _

theorem residualPrimeBlock_subset (j : ℕ) :
    residualPrimeBlock j ⊆ primeBlock j :=
  Finset.sdiff_subset

theorem retainedPrimeBlock_disjoint_residual (j : ℕ) :
    Disjoint (retainedPrimeBlock j) (residualPrimeBlock j) :=
  Finset.disjoint_sdiff

theorem retainedPrimeBlock_union_residual (j : ℕ) :
    retainedPrimeBlock j ∪ residualPrimeBlock j = primeBlock j :=
  Finset.union_sdiff_of_subset (retainedPrimeBlock_subset j)

noncomputable def retainedPrimeBlockMass (j : ℕ) : ℝ :=
  ∑ p ∈ retainedPrimeBlock j, 1 / (p : ℝ)

noncomputable def residualPrimeBlockMass (j : ℕ) : ℝ :=
  ∑ p ∈ residualPrimeBlock j, 1 / (p : ℝ)

theorem retainedPrimeBlockMass_le_log_two (j : ℕ) :
    retainedPrimeBlockMass j ≤ Real.log 2 :=
  maximalCappedSubset_weight_le _ _ _ _

theorem reciprocal_prime_nonneg {j p : ℕ} (_hp : p ∈ primeBlock j) :
    0 ≤ 1 / (p : ℝ) := by positivity

theorem reciprocal_prime_le_inv_blockEndpoint
    {j p : ℕ} (hp : p ∈ primeBlock j) :
    1 / (p : ℝ) ≤ 1 / (blockEndpoint j : ℝ) := by
  have hpData := mem_primeBlock.mp hp
  exact one_div_le_one_div_of_le (by
    exact_mod_cast blockEndpoint_pos j) (by exact_mod_cast hpData.2.1.le)

theorem inv_blockEndpoint_le_two_pow (j : ℕ) :
    1 / (blockEndpoint j : ℝ) ≤ 1 / (2 : ℝ) ^ j := by
  have hpow : 2 ^ j ≤ blockEndpoint j := by
    rw [blockEndpoint]
    exact Nat.pow_le_pow_right (by omega) (Nat.le_of_lt j.lt_two_pow_self)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  exact one_div_le_one_div_of_le hpos (by exact_mod_cast hpow)

/-- Geometric Mertens error implies geometric total mass for the discarded
overflow primes. -/
theorem residualPrimeBlockMass_le
    {C : ℝ} (hC : 0 ≤ C) {j : ℕ}
    (hmass : |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j) :
    residualPrimeBlockMass j ≤ (C + 1) / (2 : ℝ) ^ j := by
  have htotal : primeBlockMass j ≤ Real.log 2 + C / (2 : ℝ) ^ j := by
    linarith [le_of_abs_le hmass]
  have hres := residual_weight_maximalCappedSubset_le
    (primeBlock j) (fun p ↦ 1 / (p : ℝ)) (Real.log 2)
    (C / (2 : ℝ) ^ j) (1 / (blockEndpoint j : ℝ))
    (Real.log_pos one_lt_two).le
    (div_nonneg hC (by positivity)) (by positivity)
    (by simpa [primeBlockMass] using htotal)
    (fun p hp ↦ reciprocal_prime_le_inv_blockEndpoint hp)
  have hinv := inv_blockEndpoint_le_two_pow j
  calc
    residualPrimeBlockMass j ≤
        C / (2 : ℝ) ^ j + 1 / (blockEndpoint j : ℝ) := hres
    _ ≤ C / (2 : ℝ) ^ j + 1 / (2 : ℝ) ^ j :=
      add_le_add le_rfl hinv
    _ = (C + 1) / (2 : ℝ) ^ j := by ring

end

end Erdos446
