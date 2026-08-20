/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.Basic

/-!
# Erdős Problem 446: the right-endpoint transfer

Ford counts divisors in `(y, z]`; the problem uses `(n, 2n)`.  This file
defines both conventions and proves that adjoining the one possible divisor
`2n` changes every relevant density by at most `1 / (2n)`.
-/

namespace Erdos446

open Filter Finset Set
open scoped Topology

/-- Number of divisors of `m` in `(y, z]`. -/
def divisorCountIoc (y z m : ℕ) : ℕ :=
  ((Finset.Ioc y z).filter fun d ↦ d ∣ m).card

/-- Integers with exactly `r` divisors in `(y, z]`. -/
def exactDivisorSetIoc (r y z : ℕ) : Set ℕ :=
  {m | divisorCountIoc y z m = r}

/-- Integers with at least one divisor in `(y, z]`. -/
def divisorSetIoc (y z : ℕ) : Set ℕ :=
  {m | 0 < divisorCountIoc y z m}

def intervalLcmIoc (y z : ℕ) : ℕ :=
  (Finset.Ioc y z).lcm id

theorem intervalLcmIoc_pos {y z : ℕ} (hy : 0 < y) :
    0 < intervalLcmIoc y z := by
  apply Nat.pos_of_ne_zero
  rw [intervalLcmIoc, Finset.lcm_ne_zero_iff]
  intro d hd
  have hyd : y < d := (Finset.mem_Ioc.mp hd).1
  simpa only [id_eq] using
    (Nat.ne_of_gt (lt_of_lt_of_le hy hyd.le))

theorem divisorCountIoc_add_intervalLcm (y z m : ℕ) :
    divisorCountIoc y z (m + intervalLcmIoc y z) =
      divisorCountIoc y z m := by
  simp only [divisorCountIoc]
  congr 1
  refine filter_congr fun d hd ↦ ?_
  rw [add_comm]
  exact Nat.dvd_add_right (Finset.dvd_lcm hd)

theorem exactDivisorSetIoc_periodic (r y z : ℕ) :
    Function.Periodic (fun m ↦ m ∈ exactDivisorSetIoc r y z)
      (intervalLcmIoc y z) := by
  intro m
  simp only [exactDivisorSetIoc, Set.mem_ofPred_eq]
  exact congrArg (fun k ↦ k = r) (divisorCountIoc_add_intervalLcm y z m)

theorem divisorSetIoc_periodic (y z : ℕ) :
    Function.Periodic (fun m ↦ m ∈ divisorSetIoc y z)
      (intervalLcmIoc y z) := by
  intro m
  simp only [divisorSetIoc, Set.mem_ofPred_eq]
  exact congrArg (fun k ↦ 0 < k) (divisorCountIoc_add_intervalLcm y z m)

/-- Ford's density of integers with exactly `r` divisors in `(y, z]`. -/
noncomputable def epsilonR (r y z : ℕ) : ℝ :=
  (((((Finset.range (intervalLcmIoc y z)).filter
    (fun m ↦ divisorCountIoc y z m = r)).card : ℕ) : ℝ) /
      (intervalLcmIoc y z : ℝ))

/-- Ford's density of integers with a divisor in `(y, z]`. -/
noncomputable def epsilon (y z : ℕ) : ℝ :=
  (((((Finset.range (intervalLcmIoc y z)).filter
    (fun m ↦ 0 < divisorCountIoc y z m)).card : ℕ) : ℝ) /
      (intervalLcmIoc y z : ℝ))

theorem exactDivisorSetIoc_hasDensity (r y z : ℕ) (hy : 0 < y) :
    (exactDivisorSetIoc r y z).HasDensity (epsilonR r y z) := by
  simpa [exactDivisorSetIoc, epsilonR] using
    hasDensity_of_periodic (fun m ↦ divisorCountIoc y z m = r)
      (intervalLcmIoc y z) (intervalLcmIoc_pos hy)
      (exactDivisorSetIoc_periodic r y z)

theorem divisorSetIoc_hasDensity (y z : ℕ) (hy : 0 < y) :
    (divisorSetIoc y z).HasDensity (epsilon y z) := by
  simpa [divisorSetIoc, epsilon] using
    hasDensity_of_periodic (fun m ↦ 0 < divisorCountIoc y z m)
      (intervalLcmIoc y z) (intervalLcmIoc_pos hy)
      (divisorSetIoc_periodic y z)

/-! ## Comparing densities through a symmetric-difference majorant -/

private theorem partialDensity_mono {S T : Set ℕ} (hST : S ⊆ T) (N : ℕ) :
    S.partialDensity Set.univ N ≤ T.partialDensity Set.univ N := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub : S ∩ Set.Iio N ⊆ T ∩ Set.Iio N :=
    fun _ hx ↦ ⟨hST hx.1, hx.2⟩
  exact_mod_cast Set.ncard_le_ncard hsub

private theorem partialDensity_union_le (S T : Set ℕ) (N : ℕ) :
    (S ∪ T).partialDensity Set.univ N ≤
      S.partialDensity Set.univ N + T.partialDensity Set.univ N := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  rw [Set.union_inter_distrib_right, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_union_le (S ∩ Set.Iio N) (T ∩ Set.Iio N)

/-- If the symmetric difference of two sets lies in a third set, the
difference of their densities is bounded by the third density. -/
theorem abs_density_sub_le_of_symmDiff_subset
    {S T D : Set ℕ} {a b c : ℝ}
    (hS : S.HasDensity a) (hT : T.HasDensity b) (hD : D.HasDensity c)
    (hsub : (S \ T) ∪ (T \ S) ⊆ D) :
    |a - b| ≤ c := by
  have hSsub : S ⊆ T ∪ D := by
    intro m hm
    by_cases hmT : m ∈ T
    · exact Or.inl hmT
    · exact Or.inr (hsub (Or.inl ⟨hm, hmT⟩))
  have hTsub : T ⊆ S ∪ D := by
    intro m hm
    by_cases hmS : m ∈ S
    · exact Or.inl hmS
    · exact Or.inr (hsub (Or.inr ⟨hm, hmS⟩))
  have hupperST : a - b - c ≤ 0 := by
    apply le_of_tendsto ((hS.sub hT).sub hD)
    exact Eventually.of_forall fun N ↦ by
      have hle := (partialDensity_mono hSsub N).trans
        (partialDensity_union_le T D N)
      linarith
  have hupperTS : b - a - c ≤ 0 := by
    apply le_of_tendsto ((hT.sub hS).sub hD)
    exact Eventually.of_forall fun N ↦ by
      have hle := (partialDensity_mono hTsub N).trans
        (partialDensity_union_le S D N)
      linarith
  rw [abs_le]
  constructor <;> linarith

/-! ## Multiples and the endpoint identity -/

def multipleSet (q : ℕ) : Set ℕ := {m | q ∣ m}

theorem multipleSet_periodic (q : ℕ) :
    Function.Periodic (fun m ↦ m ∈ multipleSet q) q := by
  intro m
  simp only [multipleSet, Set.mem_ofPred_eq]
  rw [add_comm]
  exact propext (Nat.dvd_add_right dvd_rfl)

private theorem card_filter_dvd_range (q : ℕ) (hq : 0 < q) :
    ((Finset.range q).filter fun m ↦ q ∣ m).card = 1 := by
  have hset : (Finset.range q).filter (fun m ↦ q ∣ m) = {0} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hmq, hdiv⟩
      by_contra hm0
      have hqm : q ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdiv
      omega
    · intro hm
      subst m
      simp [hq]
  rw [hset, Finset.card_singleton]

theorem multipleSet_hasDensity (q : ℕ) (hq : 0 < q) :
    (multipleSet q).HasDensity (1 / (q : ℝ)) := by
  have h := hasDensity_of_periodic (fun m ↦ q ∣ m) q hq
    (multipleSet_periodic q)
  simpa [multipleSet, card_filter_dvd_range q hq] using h

/-- Adjoining the right endpoint adds exactly one divisor precisely on
multiples of that endpoint. -/
theorem divisorCountIoc_eq_open_add_endpoint (n m : ℕ) (hn : 0 < n) :
    divisorCountIoc n (2 * n) m =
      divisorCount n m + if 2 * n ∣ m then 1 else 0 := by
  have hinterval : Finset.Ioc n (2 * n) =
      insert (2 * n) (Finset.Ioo n (2 * n)) := by
    ext d
    simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  by_cases hend : 2 * n ∣ m
  · rw [divisorCountIoc, divisorCount, hinterval, Finset.filter_insert]
    simp [hend]
  · rw [divisorCountIoc, divisorCount, hinterval, Finset.filter_insert]
    simp [hend]

theorem divisorSet_endpoint_symmDiff_subset (n : ℕ) (hn : 0 < n) :
    (divisorSet n \ divisorSetIoc n (2 * n)) ∪
      (divisorSetIoc n (2 * n) \ divisorSet n) ⊆ multipleSet (2 * n) := by
  intro m hm
  simp only [divisorSet, divisorSetIoc, multipleSet, Set.mem_union,
    Set.mem_diff, Set.mem_ofPred_eq] at hm ⊢
  by_contra hend
  have heq := divisorCountIoc_eq_open_add_endpoint n m hn
  rw [if_neg hend, add_zero] at heq
  rcases hm with hm | hm
  · exact hm.2 (heq.symm ▸ hm.1)
  · exact hm.2 (heq ▸ hm.1)

theorem exactDivisorSet_endpoint_symmDiff_subset (r n : ℕ) (hn : 0 < n) :
    (exactDivisorSet r n \ exactDivisorSetIoc r n (2 * n)) ∪
      (exactDivisorSetIoc r n (2 * n) \ exactDivisorSet r n) ⊆
        multipleSet (2 * n) := by
  intro m hm
  simp only [exactDivisorSet, exactDivisorSetIoc, multipleSet, Set.mem_union,
    Set.mem_diff, Set.mem_ofPred_eq] at hm ⊢
  by_contra hend
  have heq := divisorCountIoc_eq_open_add_endpoint n m hn
  rw [if_neg hend, add_zero] at heq
  rcases hm with hm | hm
  · exact hm.2 (heq ▸ hm.1)
  · exact hm.2 (heq.symm ▸ hm.1)

/-- Quantitative right-endpoint error for the union density. -/
theorem abs_delta_sub_epsilon_le (n : ℕ) (hn : 0 < n) :
    |delta n - epsilon n (2 * n)| ≤ 1 / (2 * n : ℝ) := by
  have h := abs_density_sub_le_of_symmDiff_subset
    (divisorSet_hasDensity n) (divisorSetIoc_hasDensity n (2 * n) hn)
    (multipleSet_hasDensity (2 * n) (by omega))
    (divisorSet_endpoint_symmDiff_subset n hn)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- Quantitative right-endpoint error for every exact multiplicity. -/
theorem abs_deltaR_sub_epsilonR_le (r n : ℕ) (hn : 0 < n) :
    |deltaR r n - epsilonR r n (2 * n)| ≤ 1 / (2 * n : ℝ) := by
  have h := abs_density_sub_le_of_symmDiff_subset
    (exactDivisorSet_hasDensity r n)
    (exactDivisorSetIoc_hasDensity r n (2 * n) hn)
    (multipleSet_hasDensity (2 * n) (by omega))
    (exactDivisorSet_endpoint_symmDiff_subset r n hn)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

end Erdos446
