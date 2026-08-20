/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperComplementaryRoughShell

/-!
# Erdős Problem 446: complementary shells into cluster fibers

The complementary factor in a dyadic ambient shell lies in one of four
dyadic factor windows.  This file turns that observation into a literal
finite cover by the admissible prime fibers of the cluster-window theorem.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

/-- Smooth squarefree lower factors at the original cutoff. -/
def fordTargetSmoothFactors (X y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun a ↦
    Squarefree a ∧ a.primeFactors ⊆ primesUpTo (2 * y)

/-- Admissible pairs at coordinate scale `w`, restricted to the original
smoothness cutoff `2*y`. -/
def fordTargetAdmissiblePairs (X y w : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (fordTargetSmoothFactors X y ×ˢ Nat.primesLE (2 * y)).filter fun ap ↦
    (ap.1, ap.2) ∈ fordAdmissibleLargestPrimePairs X w (2 * w)

theorem mem_fordTargetAdmissiblePairs {X y w a p : ℕ} :
    (a, p) ∈ fordTargetAdmissiblePairs X y w ↔
      a ∈ fordTargetSmoothFactors X y ∧ p.Prime ∧ p ≤ 2 * y ∧
        (a, p) ∈ fordAdmissibleLargestPrimePairs X w (2 * w) := by
  classical
  rw [fordTargetAdmissiblePairs, Finset.mem_filter, Finset.mem_product]
  simp only [Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨ha, hpLe, hpPrime⟩, hap⟩
    exact ⟨ha, hpPrime, hpLe, hap⟩
  · rintro ⟨ha, hpPrime, hpLe, hap⟩
    exact ⟨⟨ha, hpLe, hpPrime⟩, hap⟩

theorem complementaryWitness_mem_admissible_of_interval
    {X₀ X₁ y z a p w : ℕ}
    {s : ℕ}
    (hsChosen : ∃ n m t b, X₀ < n ∧ n ≤ X₁ ∧ Squarefree n ∧
      y < m ∧ m ≤ z ∧ m ∣ n ∧ 1 < m ∧ 1 < n / m ∧
      s ∣ n ∧ t ∣ n ∧ 1 < s ∧ 1 < t ∧
      (s = m ∧ t = n / m ∨ s = n / m ∧ t = m) ∧
      Erdos469.largestPrimeFactor s < Erdos469.largestPrimeFactor t ∧
      p = Erdos469.largestPrimeFactor s ∧
      a = fordLowerPrimePart n p ∧ b = fordUpperPrimePart n p ∧
      p.Prime ∧ 0 < a ∧ p < b ∧ n = a * p * b ∧
      Erdos387.IsZRough p b ∧ s / p ∈ a.divisors ∧ s = (s / p) * p)
    (hws : w < s) (hs2w : s ≤ 2 * w) :
    (a, p) ∈ fordAdmissibleLargestPrimePairs X₁ w (2 * w) := by
  obtain ⟨n, m, t, b, hn0, hn1, hnSq, hym, hmz, hm,
    hmOne, heOne, hs, ht, hsOne, htOne, hst, hlt, hp, ha, hb,
    hpPrime, haPos, hpb, hnprod, hrough, hsdiv, hseq⟩ := hsChosen
  have hpDvdS : p ∣ s := by
    rw [hp]
    exact (Erdos469.largestPrimeFactor_spec hsOne).dvd
  have hpLeS : p ≤ s := Nat.le_of_dvd (by omega) hpDvdS
  have hapDvd : a * p ∣ n := by
    exact ⟨b, hnprod⟩
  have haDvd : a ∣ n := (dvd_mul_right a p).trans hapDvd
  have haLe : a ≤ X₁ :=
    (Nat.le_of_dvd (Nat.zero_lt_of_lt hn0) haDvd).trans hn1
  have hapLe : a * p ≤ X₁ :=
    (Nat.le_of_dvd (Nat.zero_lt_of_lt hn0) hapDvd).trans hn1
  rw [mem_fordAdmissibleLargestPrimePairs]
  refine ⟨haPos, haLe, hpLeS.trans hs2w, hpPrime,
    hnSq.squarefree_of_dvd haDvd, ?_, hapLe, ?_⟩
  · intro q hq hqa
    rw [ha] at hqa
    exact prime_lt_of_dvd_fordLowerPrimePart hq hqa
  · rw [hseq] at hws hs2w
    exact ⟨s / p, hsdiv, hws, hs2w⟩

private theorem source_chosen_data
    {X₀ X₁ y z a p : ℕ}
    (hsrc : fordComplementaryShellWitness X₀ X₁ y z a p) :
    ∃ s n m t b, X₀ < n ∧ n ≤ X₁ ∧ Squarefree n ∧
      y < m ∧ m ≤ z ∧ m ∣ n ∧ 1 < m ∧ 1 < n / m ∧
      s ∣ n ∧ t ∣ n ∧ 1 < s ∧ 1 < t ∧
      (s = m ∧ t = n / m ∨ s = n / m ∧ t = m) ∧
      Erdos469.largestPrimeFactor s < Erdos469.largestPrimeFactor t ∧
      p = Erdos469.largestPrimeFactor s ∧
      a = fordLowerPrimePart n p ∧ b = fordUpperPrimePart n p ∧
      p.Prime ∧ 0 < a ∧ p < b ∧ n = a * p * b ∧
      Erdos387.IsZRough p b ∧ s / p ∈ a.divisors ∧ s = (s / p) * p := by
  obtain ⟨n, m, s, t, b, h⟩ := hsrc
  exact ⟨s, n, m, t, b, h⟩

/-- An actual pair from `(X/2,X]` lies either in the original divisor
window or in one of four dyadic complementary-factor windows. -/
theorem fordComplementaryShellPairs_subset_five_target_fibers
    {X Y y : ℕ} (hy : 1 ≤ y) (hyY : y ≤ Y) (hX : 8 * y ≤ X) :
    fordComplementaryShellPairs (X / 2) X y (2 * y) ⊆
      fordTargetAdmissiblePairs X Y y ∪
      fordTargetAdmissiblePairs X Y (X / (8 * y)) ∪
      fordTargetAdmissiblePairs X Y (2 * (X / (8 * y))) ∪
      fordTargetAdmissiblePairs X Y (4 * (X / (8 * y))) ∪
      fordTargetAdmissiblePairs X Y (8 * (X / (8 * y))) := by
  classical
  intro ap hap
  rcases ap with ⟨a, p⟩
  have hapData := mem_fordComplementaryShellPairs.mp hap
  have hsrc := hapData.2.2.2.2
  obtain ⟨s, n, m, t, b, hn0, hn1, hnSq, hym, hm2y, hm,
    hmOne, heOne, hs, ht, hsOne, htOne, hst, hlt, hp, ha, hb,
    hpPrime, haPos, hpb, hnprod, hrough, hsdiv, hseq⟩ :=
      source_chosen_data hsrc
  let W := X / (8 * y)
  have hWpos : 0 < W := by
    dsimp [W]
    exact Nat.div_pos hX (by omega)
  have haSmooth : a ∈ fordTargetSmoothFactors X Y := by
    rw [fordTargetSmoothFactors, Finset.mem_filter, Finset.mem_Icc]
    have hapDvd : a * p ∣ n := ⟨b, hnprod⟩
    have haDvd : a ∣ n := (dvd_mul_right a p).trans hapDvd
    have haLe := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn0) haDvd).trans hn1
    refine ⟨⟨haPos, haLe⟩, hnSq.squarefree_of_dvd haDvd, ?_⟩
    intro q hq
    have hqPrime := Nat.prime_of_mem_primeFactors hq
    have hqLt : q < p := by
      have hqd := Nat.dvd_of_mem_primeFactors hq
      rw [ha] at hqd
      exact prime_lt_of_dvd_fordLowerPrimePart hqPrime hqd
    rw [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hqPrime.two_le,
      hqLt.le.trans (hapData.2.2.1.trans (Nat.mul_le_mul_left 2 hyY))⟩,
      hqPrime⟩
  have hpCut : p.Prime ∧ p ≤ 2 * Y :=
    ⟨hpPrime, hapData.2.2.1.trans (Nat.mul_le_mul_left 2 hyY)⟩
  have chosen : ∃ n m t b, X / 2 < n ∧ n ≤ X ∧ Squarefree n ∧
      y < m ∧ m ≤ 2 * y ∧ m ∣ n ∧ 1 < m ∧ 1 < n / m ∧
      s ∣ n ∧ t ∣ n ∧ 1 < s ∧ 1 < t ∧
      (s = m ∧ t = n / m ∨ s = n / m ∧ t = m) ∧
      Erdos469.largestPrimeFactor s < Erdos469.largestPrimeFactor t ∧
      p = Erdos469.largestPrimeFactor s ∧
      a = fordLowerPrimePart n p ∧ b = fordUpperPrimePart n p ∧
      p.Prime ∧ 0 < a ∧ p < b ∧ n = a * p * b ∧
      Erdos387.IsZRough p b ∧ s / p ∈ a.divisors ∧ s = (s / p) * p :=
    ⟨n, m, t, b, hn0, hn1, hnSq, hym, hm2y, hm, hmOne, heOne,
      hs, ht, hsOne, htOne, hst, hlt, hp, ha, hb, hpPrime, haPos,
      hpb, hnprod, hrough, hsdiv, hseq⟩
  rcases hst with hsm | hse
  · simp only [Finset.mem_union]
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    rw [mem_fordTargetAdmissiblePairs]
    refine ⟨haSmooth, hpCut.1, hpCut.2, ?_⟩
    apply complementaryWitness_mem_admissible_of_interval
      (X₀ := X / 2) (y := y) (z := 2 * y) (s := s)
      chosen
    · simpa [hsm.1] using hym
    · simpa [hsm.1] using hm2y
  · have hsn : s * m = n := by
      rw [hse.1]
      exact Nat.div_mul_cancel hm
    have hWs : W < s := by
      by_contra hnot
      have hsW : s ≤ W := by omega
      have hnLe : n ≤ 2 * y * W := by
        rw [← hsn]
        simpa [mul_comm] using Nat.mul_le_mul hm2y hsW
      have h8W : 8 * y * W ≤ X := by
        dsimp [W]
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_div_le X (8 * y)
      have h4n : 4 * n ≤ X := by
        calc
          4 * n ≤ 4 * (2 * y * W) := Nat.mul_le_mul_left 4 hnLe
          _ = 8 * y * W := by ring
          _ ≤ X := h8W
      omega
    have hsU : s ≤ X / y := by
      apply (Nat.le_div_iff_mul_le (by omega)).2
      exact (calc
        s * y < s * m := (Nat.mul_lt_mul_left (by omega : 0 < s)).2 hym
        _ = n := by simpa [mul_comm] using hsn
        _ ≤ X := hn1).le
    have hUlt : X / y < 8 * (W + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simpa [W, mul_assoc, mul_comm, mul_left_comm] using
        Nat.lt_mul_div_succ X (by omega : 0 < 8 * y)
    have hU16 : X / y ≤ 16 * W := by
      have : 8 * (W + 1) ≤ 16 * W := by omega
      omega
    have hs16 : s ≤ 16 * W := hsU.trans hU16
    by_cases hs2 : s ≤ 2 * W
    · simp only [Finset.mem_union]
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inr
      rw [mem_fordTargetAdmissiblePairs]
      refine ⟨haSmooth, hpCut.1, hpCut.2, ?_⟩
      simpa [W] using (complementaryWitness_mem_admissible_of_interval
        (w := W) chosen hWs hs2)
    · have h2s : 2 * W < s := by omega
      by_cases hs4 : s ≤ 4 * W
      · simp only [Finset.mem_union]
        apply Or.inl
        apply Or.inl
        apply Or.inr
        rw [mem_fordTargetAdmissiblePairs]
        refine ⟨haSmooth, hpCut.1, hpCut.2, ?_⟩
        have hs4' : s ≤ 2 * (2 * W) := by omega
        simpa [W, mul_assoc] using
          (complementaryWitness_mem_admissible_of_interval
            (w := 2 * W) chosen h2s hs4')
      · have h4s : 4 * W < s := by omega
        by_cases hs8 : s ≤ 8 * W
        · simp only [Finset.mem_union]
          apply Or.inl
          apply Or.inr
          rw [mem_fordTargetAdmissiblePairs]
          refine ⟨haSmooth, hpCut.1, hpCut.2, ?_⟩
          have hs8' : s ≤ 2 * (4 * W) := by omega
          simpa [W, mul_assoc] using
            (complementaryWitness_mem_admissible_of_interval
              (w := 4 * W) chosen h4s hs8')
        · simp only [Finset.mem_union]
          apply Or.inr
          rw [mem_fordTargetAdmissiblePairs]
          refine ⟨haSmooth, hpCut.1, hpCut.2, ?_⟩
          have h8s : 8 * W < s := by omega
          have hs16' : s ≤ 2 * (8 * W) := by omega
          simpa [W, mul_assoc] using
            (complementaryWitness_mem_admissible_of_interval
              (w := 8 * W) chosen h8s hs16')

/-! ## Summing the five fibers -/

def fordTargetAdmissiblePrimeFiber (X y w a : ℕ) : Finset ℕ :=
  (Nat.primesLE (2 * y)).filter fun p ↦
    (a, p) ∈ fordAdmissibleLargestPrimePairs X w (2 * w)

theorem fordTargetAdmissiblePrimeFiber_subset
    (X y w a : ℕ) :
    fordTargetAdmissiblePrimeFiber X y w a ⊆
      fordAdmissiblePrimeFiber X w (2 * w) a := by
  intro p hp
  rw [fordTargetAdmissiblePrimeFiber, Finset.mem_filter] at hp
  rw [mem_fordAdmissiblePrimeFiber]
  exact ⟨(mem_fordAdmissibleLargestPrimePairs.mp hp.2).2.2.2.1,
    (mem_fordAdmissibleLargestPrimePairs.mp hp.2).2.2.1, hp.2⟩

theorem sum_fordTargetAdmissiblePairs_eq
    (X y w : ℕ) :
    (∑ ap ∈ fordTargetAdmissiblePairs X y w,
      1 / ((ap.1 : ℝ) * (ap.2 : ℝ) * Real.log (ap.2 : ℝ))) =
      ∑ a ∈ fordTargetSmoothFactors X y,
        (1 / (a : ℝ)) *
          ∑ p ∈ fordTargetAdmissiblePrimeFiber X y w a,
            1 / ((p : ℝ) * Real.log (p : ℝ)) := by
  classical
  unfold fordTargetAdmissiblePairs fordTargetAdmissiblePrimeFiber
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X w (2 * w)
  · simp only [hap, ↓reduceIte]
    ring
  · simp only [hap, ↓reduceIte, mul_zero]

theorem targetPrimeFiber_log_weight_le_full
    {X y w a : ℕ} :
    (∑ p ∈ fordTargetAdmissiblePrimeFiber X y w a,
      1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
      ∑ p ∈ fordAdmissiblePrimeFiber X w (2 * w) a,
        1 / ((p : ℝ) * Real.log (p : ℝ)) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (fordTargetAdmissiblePrimeFiber_subset X y w a)
  intro p hp hnot
  have hpPrime := (mem_fordAdmissiblePrimeFiber.mp hp).1
  exact one_div_nonneg.mpr
    (mul_nonneg (Nat.cast_nonneg p) hpPrime.log_pos.le)

theorem fordTargetSmoothFactors_primeFactors_injective
    {X y : ℕ} :
    Set.InjOn Nat.primeFactors (fordTargetSmoothFactors X y) := by
  intro a ha b hb hab
  have haSq := (Finset.mem_filter.mp ha).2.1
  have hbSq := (Finset.mem_filter.mp hb).2.1
  have hpa : a.primeFactors.prod id = a := by
    simpa using Nat.prod_primeFactors_of_squarefree haSq
  have hpb : b.primeFactors.prod id = b := by
    simpa using Nat.prod_primeFactors_of_squarefree hbSq
  rw [← hpa, ← hpb, hab]

theorem fordTargetSmoothFactors_primeFactors_image_subset
    (X y : ℕ) :
    (fordTargetSmoothFactors X y).image Nat.primeFactors ⊆
      (primesUpTo (2 * y)).powerset := by
  intro S hS
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hS
  rw [Finset.mem_powerset]
  exact (Finset.mem_filter.mp ha).2.2

theorem sum_fordTargetSmoothFactors_cluster_le
    (X y : ℕ) :
    (∑ a ∈ fordTargetSmoothFactors X y,
      clusterLength a / (a : ℝ) /
        Real.log (fordVariableLogArgument y a.primeFactors) ^ 2) ≤
      fordVariableDenominatorSum y (2 * y) := by
  classical
  let g : Finset ℕ → ℝ := fun S ↦
    primeSubsetClusterTerm S /
      Real.log (fordVariableLogArgument y S) ^ 2
  have hg : ∀ S, 0 ≤ g S := by
    intro S
    exact div_nonneg (primeSubsetClusterTerm_nonneg S) (sq_nonneg _)
  have hinj := fordTargetSmoothFactors_primeFactors_injective
    (X := X) (y := y)
  calc
    (∑ a ∈ fordTargetSmoothFactors X y,
      clusterLength a / (a : ℝ) /
        Real.log (fordVariableLogArgument y a.primeFactors) ^ 2) =
        ∑ a ∈ fordTargetSmoothFactors X y, g a.primeFactors := by
      apply Finset.sum_congr rfl
      intro a ha
      have haSq := (Finset.mem_filter.mp ha).2.1
      have hprod : a.primeFactors.prod id = a := by
        simpa using Nat.prod_primeFactors_of_squarefree haSq
      unfold g primeSubsetClusterTerm
      rw [hprod]
    _ = ∑ S ∈ (fordTargetSmoothFactors X y).image Nat.primeFactors,
        g S := by
      exact (Finset.sum_image hinj).symm
    _ ≤ ∑ S ∈ (primesUpTo (2 * y)).powerset, g S :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fordTargetSmoothFactors_primeFactors_image_subset X y)
        (fun S hS hnot ↦ hg S)
    _ = fordVariableDenominatorSum y (2 * y) := rfl

/-- One target-scale fiber family is bounded by the exact variable-
denominator cluster sum. -/
theorem exists_pos_targetAdmissiblePairs_weight_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y w X : ℕ, 2 ≤ y →
      (y : ℝ) ^ (2 / 3 : ℝ) ≤ (w : ℝ) →
      (∑ ap ∈ fordTargetAdmissiblePairs X y w,
        1 / ((ap.1 : ℝ) * (ap.2 : ℝ) *
          Real.log (ap.2 : ℝ))) ≤
        C * fordVariableDenominatorSum y (2 * y) := by
  obtain ⟨C, hC, hfiber⟩ :=
    exists_pos_admissiblePrimeFiber_target_log_weight_le
  refine ⟨C, hC, fun y w X hy hyw ↦ ?_⟩
  rw [sum_fordTargetAdmissiblePairs_eq]
  calc
    (∑ a ∈ fordTargetSmoothFactors X y,
        (1 / (a : ℝ)) *
          ∑ p ∈ fordTargetAdmissiblePrimeFiber X y w a,
            1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
      ∑ a ∈ fordTargetSmoothFactors X y,
        (1 / (a : ℝ)) *
          (C * clusterLength a /
            Real.log (fordVariableLogArgument y a.primeFactors) ^ 2) := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (targetPrimeFiber_log_weight_le_full).trans
        (hfiber y w X a hy hyw)
    _ = C * (∑ a ∈ fordTargetSmoothFactors X y,
        clusterLength a / (a : ℝ) /
          Real.log (fordVariableLogArgument y a.primeFactors) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ C * fordVariableDenominatorSum y (2 * y) := by
      exact mul_le_mul_of_nonneg_left
        (sum_fordTargetSmoothFactors_cluster_le X y) hC.le

def fordPairLogWeight (ap : ℕ × ℕ) : ℝ :=
  1 / ((ap.1 : ℝ) * (ap.2 : ℝ) * Real.log (ap.2 : ℝ))

theorem fordPairLogWeight_nonneg_of_target
    {X y w : ℕ} {ap : ℕ × ℕ}
    (hap : ap ∈ fordTargetAdmissiblePairs X y w) :
    0 ≤ fordPairLogWeight ap := by
  have hp := (mem_fordTargetAdmissiblePairs.mp hap).2.1
  exact one_div_nonneg.mpr
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      hp.log_pos.le)

theorem sum_union_le_add_sum_of_nonneg
    {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s ∪ t, 0 ≤ f x) :
    (∑ x ∈ s ∪ t, f x) ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have hdis : Disjoint s (t \ s) := by
    rw [Finset.disjoint_left]
    intro x hxs hxts
    exact (Finset.mem_sdiff.mp hxts).2 hxs
  have hset : s ∪ (t \ s) = s ∪ t := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [← hset, Finset.sum_union hdis]
  apply add_le_add_right
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
  intro x hx hnot
  exact hf x (Finset.mem_union_right _ hx)

/-- The actual complementary-pair weight in one dyadic ambient shell is
bounded by five copies of the variable-denominator cluster sum. -/
theorem exists_pos_complementaryShellPairs_weight_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Y y X : ℕ, 2 ≤ Y → 1 ≤ y → y ≤ Y →
      8 * y ≤ X →
      (Y : ℝ) ^ (2 / 3 : ℝ) ≤ (y : ℝ) →
      (Y : ℝ) ^ (2 / 3 : ℝ) ≤ (X / (8 * y) : ℕ) →
      (∑ ap ∈ fordComplementaryShellPairs (X / 2) X y (2 * y),
        fordPairLogWeight ap) ≤
        C * fordVariableDenominatorSum Y (2 * Y) := by
  obtain ⟨C₀, hC₀, htarget⟩ := exists_pos_targetAdmissiblePairs_weight_le
  let C : ℝ := 5 * C₀
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun Y y X hY hy hyY hX hyScale hscale ↦ ?_⟩
  let W := X / (8 * y)
  let A₀ := fordTargetAdmissiblePairs X Y y
  let A₁ := fordTargetAdmissiblePairs X Y W
  let A₂ := fordTargetAdmissiblePairs X Y (2 * W)
  let A₃ := fordTargetAdmissiblePairs X Y (4 * W)
  let A₄ := fordTargetAdmissiblePairs X Y (8 * W)
  have hsub : fordComplementaryShellPairs (X / 2) X y (2 * y) ⊆
      A₀ ∪ A₁ ∪ A₂ ∪ A₃ ∪ A₄ := by
    dsimp [A₀, A₁, A₂, A₃, A₄, W]
    exact fordComplementaryShellPairs_subset_five_target_fibers
      hy hyY hX
  have hnon : ∀ ap ∈ A₀ ∪ A₁ ∪ A₂ ∪ A₃ ∪ A₄,
      0 ≤ fordPairLogWeight ap := by
    intro ap hap
    simp only [Finset.mem_union] at hap
    rcases hap with (((h0 | h1) | h2) | h3) | h4
    · exact fordPairLogWeight_nonneg_of_target h0
    · exact fordPairLogWeight_nonneg_of_target h1
    · exact fordPairLogWeight_nonneg_of_target h2
    · exact fordPairLogWeight_nonneg_of_target h3
    · exact fordPairLogWeight_nonneg_of_target h4
  have hW : (Y : ℝ) ^ (2 / 3 : ℝ) ≤ (W : ℝ) := by
    simpa [W] using hscale
  have hA0 : (∑ ap ∈ A₀, fordPairLogWeight ap) ≤
      C₀ * fordVariableDenominatorSum Y (2 * Y) := by
    simpa [A₀, fordPairLogWeight] using htarget Y y X hY hyScale
  have hA1 : (∑ ap ∈ A₁, fordPairLogWeight ap) ≤
      C₀ * fordVariableDenominatorSum Y (2 * Y) := by
    simpa [A₁, fordPairLogWeight] using htarget Y W X hY hW
  have hA2 : (∑ ap ∈ A₂, fordPairLogWeight ap) ≤
      C₀ * fordVariableDenominatorSum Y (2 * Y) := by
    apply (show (∑ ap ∈ fordTargetAdmissiblePairs X Y (2 * W),
      fordPairLogWeight ap) ≤ _ from ?_)
    simpa [fordPairLogWeight] using htarget Y (2 * W) X hY
      (hW.trans (by exact_mod_cast (show W ≤ 2 * W by omega)))
  have hA3 : (∑ ap ∈ A₃, fordPairLogWeight ap) ≤
      C₀ * fordVariableDenominatorSum Y (2 * Y) := by
    apply (show (∑ ap ∈ fordTargetAdmissiblePairs X Y (4 * W),
      fordPairLogWeight ap) ≤ _ from ?_)
    simpa [fordPairLogWeight] using htarget Y (4 * W) X hY
      (hW.trans (by exact_mod_cast (show W ≤ 4 * W by omega)))
  have hA4 : (∑ ap ∈ A₄, fordPairLogWeight ap) ≤
      C₀ * fordVariableDenominatorSum Y (2 * Y) := by
    apply (show (∑ ap ∈ fordTargetAdmissiblePairs X Y (8 * W),
      fordPairLogWeight ap) ≤ _ from ?_)
    simpa [fordPairLogWeight] using htarget Y (8 * W) X hY
      (hW.trans (by exact_mod_cast (show W ≤ 8 * W by omega)))
  have hsource :
      (∑ ap ∈ fordComplementaryShellPairs (X / 2) X y (2 * y),
        fordPairLogWeight ap) ≤
      ∑ ap ∈ A₀ ∪ A₁ ∪ A₂ ∪ A₃ ∪ A₄, fordPairLogWeight ap :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun ap hap hnot ↦ hnon ap hap)
  calc
    (∑ ap ∈ fordComplementaryShellPairs (X / 2) X y (2 * y),
        fordPairLogWeight ap) ≤
      ∑ ap ∈ A₀ ∪ A₁ ∪ A₂ ∪ A₃ ∪ A₄,
        fordPairLogWeight ap := hsource
    _ ≤ (∑ ap ∈ A₀, fordPairLogWeight ap) +
          (∑ ap ∈ A₁, fordPairLogWeight ap) +
        (∑ ap ∈ A₂, fordPairLogWeight ap) +
      (∑ ap ∈ A₃, fordPairLogWeight ap) +
        ∑ ap ∈ A₄, fordPairLogWeight ap := by
      have h01 := sum_union_le_add_sum_of_nonneg A₀ A₁ fordPairLogWeight
        (fun ap hap ↦ hnon ap (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_left _ hap))))
      have h012 := sum_union_le_add_sum_of_nonneg (A₀ ∪ A₁) A₂
        fordPairLogWeight
        (fun ap hap ↦ hnon ap (Finset.mem_union_left _
          (Finset.mem_union_left _ hap)))
      have h0123 := sum_union_le_add_sum_of_nonneg (A₀ ∪ A₁ ∪ A₂) A₃
        fordPairLogWeight
        (fun ap hap ↦ hnon ap (Finset.mem_union_left _ hap))
      have h01234 := sum_union_le_add_sum_of_nonneg
        (A₀ ∪ A₁ ∪ A₂ ∪ A₃) A₄ fordPairLogWeight hnon
      linarith
    _ ≤ C₀ * fordVariableDenominatorSum Y (2 * Y) +
          C₀ * fordVariableDenominatorSum Y (2 * Y) +
        C₀ * fordVariableDenominatorSum Y (2 * Y) +
      C₀ * fordVariableDenominatorSum Y (2 * Y) +
        C₀ * fordVariableDenominatorSum Y (2 * Y) := by
      gcongr
    _ = C * fordVariableDenominatorSum Y (2 * Y) := by
      dsimp [C]
      ring

/-- The squarefree shell reduction with the divisor-window scale `v` separated
from the target Ford denominator scale `Y`.  This is the form needed after
factoring off a small powerful divisor: the squarefree cofactor sees the
shorter interval `(v,2v]`, while all five largest-prime shells are still paid
for by the single target sum at `Y`. -/
theorem exists_pos_squarefreeDyadicShell_le_targetVariableDenominator :
    ∃ K : ℝ, 0 < K ∧ ∀ Y v X : ℕ, 2 ≤ Y → 1 ≤ v → v ≤ Y →
      8 * v ≤ X →
      (Y : ℝ) ^ (2 / 3 : ℝ) ≤ (v : ℝ) →
      (Y : ℝ) ^ (2 / 3 : ℝ) ≤ (X / (8 * v) : ℕ) →
      ((squarefreeDivisorShell (X / 2) X v (2 * v)).card : ℝ) ≤
        (2 * v + 1 : ℕ) +
          K * (X : ℝ) * fordVariableDenominatorSum Y (2 * Y) := by
  obtain ⟨B, hB, hsieve⟩ :=
    exists_pos_squarefreeDivisorShell_le_complementary_weight
  obtain ⟨C, hC, hcluster⟩ :=
    exists_pos_complementaryShellPairs_weight_le
  let K : ℝ := B * C
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun Y v X hY hv hvY hX hvscale hW ↦ ?_⟩
  have hbase := hsieve (X / 2) X v (2 * v) hv
  have hweights := hcluster Y v X hY hv hvY hX hvscale hW
  unfold fordPairLogWeight at hweights
  calc
    ((squarefreeDivisorShell (X / 2) X v (2 * v)).card : ℝ) ≤
        (2 * v + 1 : ℕ) + B * (X : ℝ) *
          (∑ ap ∈ fordComplementaryShellPairs (X / 2) X v (2 * v),
            1 / ((ap.1 : ℝ) * (ap.2 : ℝ) *
              Real.log (ap.2 : ℝ))) := hbase
    _ ≤ (2 * v + 1 : ℕ) + B * (X : ℝ) *
          (C * fordVariableDenominatorSum Y (2 * Y)) := by
      gcongr
    _ = (2 * v + 1 : ℕ) + K * (X : ℝ) *
          fordVariableDenominatorSum Y (2 * Y) := by
      dsimp [K]
      ring

/-- Source-faithful squarefree shell reduction all the way to Ford's
variable-denominator cluster sum. -/
theorem exists_pos_squarefreeDyadicShell_le_variableDenominator :
    ∃ K : ℝ, 0 < K ∧ ∀ y X : ℕ, 2 ≤ y → 8 * y ≤ X →
      (y : ℝ) ^ (2 / 3 : ℝ) ≤ (X / (8 * y) : ℕ) →
      ((squarefreeDivisorShell (X / 2) X y (2 * y)).card : ℝ) ≤
        (2 * y + 1 : ℕ) +
          K * (X : ℝ) * fordVariableDenominatorSum y (2 * y) := by
  obtain ⟨B, hB, hsieve⟩ :=
    exists_pos_squarefreeDivisorShell_le_complementary_weight
  obtain ⟨C, hC, hcluster⟩ :=
    exists_pos_complementaryShellPairs_weight_le
  let K : ℝ := B * C
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun y X hy hX hscale ↦ ?_⟩
  have hbase := hsieve (X / 2) X y (2 * y) (by omega)
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (show 1 ≤ y by omega)
  have hyPow : (y : ℝ) ^ (2 / 3 : ℝ) ≤ (y : ℝ) :=
    Real.rpow_le_self_of_one_le hyR (by norm_num)
  have hweights := hcluster y y X hy (by omega) (by omega) hX hyPow hscale
  unfold fordPairLogWeight at hweights
  calc
    ((squarefreeDivisorShell (X / 2) X y (2 * y)).card : ℝ) ≤
        (2 * y + 1 : ℕ) + B * (X : ℝ) *
          (∑ ap ∈ fordComplementaryShellPairs (X / 2) X y (2 * y),
            1 / ((ap.1 : ℝ) * (ap.2 : ℝ) *
              Real.log (ap.2 : ℝ))) := hbase
    _ ≤ (2 * y + 1 : ℕ) + B * (X : ℝ) *
          (C * fordVariableDenominatorSum y (2 * y)) := by
      gcongr
    _ = (2 * y + 1 : ℕ) + K * (X : ℝ) *
          fordVariableDenominatorSum y (2 * y) := by
      dsimp [K]
      ring

/-- The squarefree dyadic shell estimate after the proved
Ford--Koukoulopoulos denominator-removal lemma. -/
theorem exists_pos_squarefreeDyadicShell_le_clusterMass :
    ∃ K : ℝ, 0 < K ∧ ∀ y X : ℕ, 2 ≤ y → 8 * y ≤ X →
      (y : ℝ) ^ (2 / 3 : ℝ) ≤ (X / (8 * y) : ℕ) →
      ((squarefreeDivisorShell (X / 2) X y (2 * y)).card : ℝ) ≤
        (2 * y + 1 : ℕ) +
          K * (X : ℝ) * squarefreeClusterMass (2 * y) /
            Real.log (y : ℝ) ^ 2 := by
  obtain ⟨K₀, hK₀, hshell⟩ :=
    exists_pos_squarefreeDyadicShell_le_variableDenominator
  obtain ⟨D, hD, hden⟩ :=
    exists_pos_fordDyadicVariableDenominatorSum_le
  let K : ℝ := K₀ * D
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun y X hy hX hscale ↦ ?_⟩
  have hbase := hshell y X hy hX hscale
  have hremove := hden y hy
  unfold fordDyadicVariableDenominatorSum at hremove
  calc
    ((squarefreeDivisorShell (X / 2) X y (2 * y)).card : ℝ) ≤
        (2 * y + 1 : ℕ) + K₀ * (X : ℝ) *
          fordVariableDenominatorSum y (2 * y) := hbase
    _ ≤ (2 * y + 1 : ℕ) + K₀ * (X : ℝ) *
          (D * squarefreeClusterMass (2 * y) /
            Real.log (y : ℝ) ^ 2) := by
      gcongr
    _ = (2 * y + 1 : ℕ) +
          K * (X : ℝ) * squarefreeClusterMass (2 * y) /
            Real.log (y : ℝ) ^ 2 := by
      dsimp [K]
      ring

end

end Erdos446
