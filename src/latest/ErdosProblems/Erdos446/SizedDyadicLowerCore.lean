/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.DyadicLowerCore
import ErdosProblems.Erdos446.SizedBlockBounds

/-!
# Erdős Problem 446: size-closed finite lower theorem

This version of the finite lower theorem uses the size-truncated capped
compositions.  The product bound and every divisor-scale condition are then
automatic at `fordConstructionScale M K`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem sizedCappedBlockFamilies_pairwiseDisjoint (M K : ℕ) :
    ((sizedCappedCompositions M K : Finset (Fin K → ℕ)) :
      Set (Fin K → ℕ)).PairwiseDisjoint (compositionBlockFamily M) := by
  intro b hb c hc hbc
  apply blockFamily_disjoint_of_ne
  by_contra hnone
  push_neg at hnone
  apply hbc
  funext i
  simpa only [extendComposition_fin] using hnone i i.isLt

theorem sizedBlock_partitioned_lower
    {N y B M K : ℕ} {R T : ℝ}
    (hK : 0 < K)
    (hN : 3 ≤ N)
    (hy3 : 3 ≤ y)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
      dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ))
    (hy : 0 < y) (hBy : B ≤ 2 * y)
    (hbound : ∀ b ∈ sizedCappedCompositions M K,
      ∀ a ∈ compositionBlockFamily M b, a ≤ B)
    (hBsq : B * B < y)
    (hscale : ∀ b ∈ sizedCappedCompositions M K,
      ∀ a ∈ compositionBlockFamily M b, ∀ d ∈ a.divisors,
        N ≤ y / d ∧ y ≤ (y / d) ^ 2)
    (hR : 0 ≤ R) (hT : 0 < T)
    (hW : ∀ b ∈ sizedCappedCompositions M K,
      0 < ∑ a ∈ compositionBlockFamily M b,
        (closePairCount a : ℝ) / a)
    (hlower : ∀ b ∈ sizedCappedCompositions M K,
      R / compositionFactorial b ≤
        ∑ a ∈ compositionBlockFamily M b,
          (a.divisors.card : ℝ) / a)
    (hupper : ∀ b ∈ sizedCappedCompositions M K,
      compositionFactorial b *
          (∑ a ∈ compositionBlockFamily M b,
            (closePairCount a : ℝ) / a) ≤
        T * compositionPenalty b) :
    smallPrimeEulerDensity (2 * y) *
        (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
          (R ^ 2 / T) *
          (∑ b ∈ sizedCappedCompositions M K,
            compositionCycleWeight b)) ≤
      epsilon y (2 * y) := by
  let c : ℝ := (1 / 96 : ℝ) / Real.log (y : ℝ)
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpart := ford_partitioned_cluster_lower_reduction
    (I := sizedCappedCompositions M K)
    (A := compositionBlockFamily M)
    hN hprime hy hBy (sizedCappedBlockFamilies_pairwiseDisjoint M K)
    (fun _b _hb a ha ↦ blockFamily_pos ha)
    hbound hBsq
    (fun _b _hb a ha ↦ blockFamily_squarefree ha)
    hscale hW
  have hterm : ∀ b ∈ sizedCappedCompositions M K,
      c * (R ^ 2 / T) * compositionCycleWeight b ≤
        (c *
            (∑ a ∈ compositionBlockFamily M b,
              (a.divisors.card : ℝ) / a) ^ 2) /
          (∑ a ∈ compositionBlockFamily M b,
            (closePairCount a : ℝ) / a) := by
    intro b hb
    have hfac : 0 < compositionFactorial b := by
      dsimp [compositionFactorial]
      positivity
    have hpen : 0 < compositionPenalty b :=
      compositionPenalty_pos_of_pos_length hK b
    have hS : 0 ≤ ∑ a ∈ compositionBlockFamily M b,
        (a.divisors.card : ℝ) / a := by
      apply Finset.sum_nonneg
      intro a ha
      exact div_nonneg (by positivity) (by positivity)
    have hq := cycleWeight_le_clusterQuotient hR hT hfac hpen hS
      (hW b hb) (hlower b hb) (hupper b hb)
    rw [compositionCycleWeight]
    calc
      c * (R ^ 2 / T) *
          (1 / (compositionFactorial b * compositionPenalty b)) =
          c * ((R ^ 2 / T) *
            (1 / (compositionFactorial b * compositionPenalty b))) := by ring
      _ ≤ c *
          ((∑ a ∈ compositionBlockFamily M b,
              (a.divisors.card : ℝ) / a) ^ 2 /
            (∑ a ∈ compositionBlockFamily M b,
              (closePairCount a : ℝ) / a)) :=
        mul_le_mul_of_nonneg_left hq hc
      _ = _ := by ring
  calc
    smallPrimeEulerDensity (2 * y) *
        (c * (R ^ 2 / T) *
          (∑ b ∈ sizedCappedCompositions M K,
            compositionCycleWeight b)) =
        smallPrimeEulerDensity (2 * y) *
          (∑ b ∈ sizedCappedCompositions M K,
            c * (R ^ 2 / T) * compositionCycleWeight b) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ smallPrimeEulerDensity (2 * y) *
        (∑ b ∈ sizedCappedCompositions M K,
          (c *
              (∑ a ∈ compositionBlockFamily M b,
                (a.divisors.card : ℝ) / a) ^ 2) /
            (∑ a ∈ compositionBlockFamily M b,
              (closePairCount a : ℝ) / a)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum hterm
      · exact smallPrimeEulerDensity_nonneg _
    _ ≤ epsilon y (2 * y) := by simpa only [c] using hpart

theorem ford_sized_dyadic_lower_core
    {N M K y : ℕ} {C E : ℝ}
    (hM : 3 ≤ M) (hK : 0 < K) (hC : 0 ≤ C)
    (hN : 3 ≤ N)
    (hNB : N ≤ fordConstructionBound M K)
    (hscaleY : fordConstructionScale M K ≤ y)
    (hendpoint : ∀ i : Fin K, N ≤ blockEndpoint (M + i))
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
      dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ))
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
        (((1 / 96 : ℝ) /
            Real.log (y : ℝ)) *
          ((((2 * Real.log 2 : ℝ) ^ K / 2) ^ 2 /
            ((2 * Real.log 2 : ℝ) ^ K * Real.exp E *
              (2 + 56 /
                (Real.log 2 ^ 2 * (2 : ℝ) ^ M)))) *
            ((1 / 2 : ℝ) *
              ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ))))) ≤
      epsilon y (2 * y) := by
  let B := fordConstructionBound M K
  let R : ℝ := (2 * Real.log 2 : ℝ) ^ K / 2
  let T : ℝ := (2 * Real.log 2 : ℝ) ^ K * Real.exp E *
    (2 + 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hy3 : 3 ≤ y := by
    have hscale3 : 3 ≤ fordConstructionScale M K := by
      have hB2 : 2 ≤ B := fordConstructionBound_one_lt M K
      rw [show fordConstructionScale M K = B ^ 4 by
        exact fordConstructionScale_eq_pow M K]
      have : 2 ^ 4 ≤ B ^ 4 := Nat.pow_le_pow_left hB2 4
      norm_num at this ⊢
      omega
    exact hscale3.trans hscaleY
  have hlower : ∀ b ∈ sizedCappedCompositions M K,
      R / compositionFactorial b ≤
        ∑ a ∈ compositionBlockFamily M b,
          (a.divisors.card : ℝ) / a := by
    intro b hb
    exact compositionBlockFamily_divisorMass_lower
      (by omega : 1 ≤ M) hC
      (sizedCappedCompositions_subset_capped M K hb)
      hmass (hselect b (sizedCappedCompositions_subset_capped M K hb)) hbudget
  have hupper : ∀ b ∈ sizedCappedCompositions M K,
      compositionFactorial b *
          (∑ a ∈ compositionBlockFamily M b,
            (closePairCount a : ℝ) / a) ≤
        T * compositionPenalty b := by
    intro b hb
    exact compositionBlockFamily_closeWeight_upper
      (by omega : 1 ≤ M) hK hC
      (sizedCappedCompositions_subset_capped M K hb)
      hmass hhalf hE hN hendpoint
      (fun t ht ↦ (hprime t ht).2)
  have hW : ∀ b ∈ sizedCappedCompositions M K,
      0 < ∑ a ∈ compositionBlockFamily M b,
        (closePairCount a : ℝ) / a := by
    intro b hb
    have hfac : 0 < compositionFactorial b := by
      dsimp [compositionFactorial]
      positivity
    have hposLower : 0 < R / compositionFactorial b := by
      dsimp [R]
      positivity
    have hdivPos : 0 < ∑ a ∈ compositionBlockFamily M b,
        (a.divisors.card : ℝ) / a :=
      lt_of_lt_of_le hposLower (hlower b hb)
    exact lt_of_lt_of_le hdivPos (blockFamily_divisorMass_le_closeWeight b)
  have hassembly := sizedBlock_partitioned_lower
    (N := N) (y := y) (B := B) (M := M) (K := K)
    (R := R) (T := T) hK hN hy3 hprime (by omega)
    ((fordConstructionBound_le_two_scale M K).trans (by omega))
    (fun b hb a ha ↦ sizedBlockFamily_le_constructionBound hb ha)
    ((fordConstructionBound_sq_lt_scale M K).trans_le hscaleY)
    (fun b hb a ha d hd ↦ sizedBlockFamily_scale_of_le hNB hscaleY hb ha hd)
    hR hT hW hlower hupper
  have hcap := sizedCappedComposition_cycleWeight_lower hM hK
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
            (∑ b ∈ sizedCappedCompositions M K,
              compositionCycleWeight b))) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left hcap hratio
          · exact hc
        · exact heuler
    _ ≤ epsilon y (2 * y) := by
      simpa only [mul_assoc] using hassembly

end Erdos446
