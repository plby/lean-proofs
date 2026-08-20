/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.BlockCloseBounds

/-!
# Erdős Problem 446: finite dyadic lower theorem

This file assembles the exact-support sieve, the partitioned prime-cluster
reduction, sharp block products, and the capped-composition theorem.  The
remaining hypotheses are solely the eventual choice of the fixed initial
block and the elementary size comparison between the block family and the
dyadic endpoint.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem blockFamily_divisorMass_le_closeWeight
    {M K : ℕ} (b : Fin K → ℕ) :
    (∑ a ∈ compositionBlockFamily M b,
        (a.divisors.card : ℝ) / a) ≤
      ∑ a ∈ compositionBlockFamily M b,
        (closePairCount a : ℝ) / a := by
  apply Finset.sum_le_sum
  intro a ha
  apply div_le_div_of_nonneg_right
  · exact_mod_cast card_divisors_le_closePairCount a
  · positivity

/-- Ford's complete finite lower-bound assembly, prior only to choosing the
fixed block cutoff and relating `K` to `log log y`. -/
theorem ford_dyadic_lower_core
    {N y B M K : ℕ} {C E : ℝ}
    (hM : 3 ≤ M) (hK : 0 < K) (hC : 0 ≤ C)
    (hN : 3 ≤ N)
    (hendpoint : ∀ i : Fin K, N ≤ blockEndpoint (M + i))
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
      dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ))
    (hy3 : 3 ≤ y) (hBy : B ≤ 2 * y)
    (hbound : ∀ b ∈ cappedCompositions M K,
      ∀ a ∈ compositionBlockFamily M b, a ≤ B)
    (hBsq : B * B < y)
    (hscale : ∀ b ∈ cappedCompositions M K,
      ∀ a ∈ compositionBlockFamily M b, ∀ d ∈ a.divisors,
        N ≤ y / d ∧ y ≤ (y / d) ^ 2)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hselect : ∀ b ∈ cappedCompositions M K, ∀ i : Fin K,
      (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
        primeBlockMass (M + i))
    (hbudget :
      (4 * (M * M) * C + 12 * (M * M) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ M) ≤ 1 / 2)
    (hhalf : ∀ i : Fin K,
      Real.log 2 / 2 ≤ primeBlockMass (M + i))
    (hE : 4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ E) :
    smallPrimeEulerDensity (2 * y) *
        (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
          ((((2 * Real.log 2 : ℝ) ^ K / 2) ^ 2 /
            ((2 * Real.log 2 : ℝ) ^ K * Real.exp E *
              (2 + 56 /
                (Real.log 2 ^ 2 * (2 : ℝ) ^ M)))) *
            ((1 / 2 : ℝ) *
              ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ))))) ≤
      epsilon y (2 * y) := by
  let R : ℝ := (2 * Real.log 2 : ℝ) ^ K / 2
  let T : ℝ := (2 * Real.log 2 : ℝ) ^ K * Real.exp E *
    (2 + 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hlower : ∀ b ∈ cappedCompositions M K,
      R / compositionFactorial b ≤
        ∑ a ∈ compositionBlockFamily M b,
          (a.divisors.card : ℝ) / a := by
    intro b hb
    exact compositionBlockFamily_divisorMass_lower
      (by omega : 1 ≤ M) hC hb hmass (hselect b hb) hbudget
  have hupper : ∀ b ∈ cappedCompositions M K,
      compositionFactorial b *
          (∑ a ∈ compositionBlockFamily M b,
            (closePairCount a : ℝ) / a) ≤
        T * compositionPenalty b := by
    intro b hb
    exact compositionBlockFamily_closeWeight_upper
      (by omega : 1 ≤ M) hK hC hb hmass hhalf hE
      hN hendpoint
      (fun t ht ↦ (hprime t ht).2)
  have hW : ∀ b ∈ cappedCompositions M K,
      0 < ∑ a ∈ compositionBlockFamily M b,
        (closePairCount a : ℝ) / a := by
    intro b hb
    have hfac : 0 < compositionFactorial b := by
      dsimp [compositionFactorial]
      positivity
    have hposLower : 0 < R / compositionFactorial b := by positivity
    have hdivPos : 0 < ∑ a ∈ compositionBlockFamily M b,
        (a.divisors.card : ℝ) / a :=
      lt_of_lt_of_le hposLower (hlower b hb)
    exact lt_of_lt_of_le hdivPos (blockFamily_divisorMass_le_closeWeight b)
  have hassembly := cappedBlock_partitioned_lower
    (R := R) (T := T) hK hN hy3 hprime (by omega) hBy
    hbound hBsq hscale hR hT hW hlower hupper
  have hcap := cappedComposition_cycleWeight_lower hM hK
  have hc : 0 ≤ (1 / 96 : ℝ) / Real.log (y : ℝ) := by
    have : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    positivity
  have hratio : 0 ≤ R ^ 2 / T := by positivity
  have heuler := smallPrimeEulerDensity_nonneg (2 * y)
  calc
    smallPrimeEulerDensity (2 * y) *
        (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
          ((R ^ 2 / T) *
            ((1 / 2 : ℝ) *
              ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ))))) ≤
      smallPrimeEulerDensity (2 * y) *
        (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
          ((R ^ 2 / T) *
            (∑ b ∈ cappedCompositions M K,
              compositionCycleWeight b))) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left hcap hratio
          · exact hc
        · exact heuler
    _ ≤ epsilon y (2 * y) := by
      simpa only [mul_assoc] using hassembly

end Erdos446
