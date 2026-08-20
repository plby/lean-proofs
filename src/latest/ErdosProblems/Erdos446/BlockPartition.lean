/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.PartitionedLower
import ErdosProblems.Erdos446.CappedCompositions
import ErdosProblems.Erdos446.BlockEstimates

/-!
# Erdős Problem 446: disjoint block partitions

Different block-cardinality vectors give disjoint families of squarefree
integers.  We combine this fact with the partitioned analytic reduction and
isolate the elementary quotient calculation which converts the two block
estimates into Ford's cyclic composition weight.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Extend a finite composition by zero so it can index `blockFamily`. -/
def extendComposition {K : ℕ} (b : Fin K → ℕ) : ℕ → ℕ :=
  fun i ↦ if h : i < K then b ⟨i, h⟩ else 0

@[simp] theorem extendComposition_fin {K : ℕ} (b : Fin K → ℕ)
    (i : Fin K) : extendComposition b i = b i := by
  simp [extendComposition, i.isLt]

/-- The block family belonging to a finite composition. -/
def compositionBlockFamily (M : ℕ) {K : ℕ} (b : Fin K → ℕ) : Finset ℕ :=
  blockFamily M K (extendComposition b)

theorem blockFamily_disjoint_of_ne {M k : ℕ} {b c : ℕ → ℕ}
    (hbc : ∃ i < k, b i ≠ c i) :
    Disjoint (blockFamily M k b) (blockFamily M k c) := by
  rw [Finset.disjoint_left]
  intro a hab hac
  obtain ⟨S, hS, hSa⟩ := mem_blockFamily.mp hab
  obtain ⟨T, hT, hTa⟩ := mem_blockFamily.mp hac
  have hST : S = T := by
    rw [← selectionProduct_primeFactors hS,
      ← selectionProduct_primeFactors hT, hSa, hTa]
  obtain ⟨i, hik, hbi⟩ := hbc
  have hb := (mem_blockSelectionSets.mp hS).2 i hik
  have hc := (mem_blockSelectionSets.mp hT).2 i hik
  rw [hST] at hb
  exact hbi (hb.symm.trans hc)

theorem cappedBlockFamilies_pairwiseDisjoint (M K : ℕ) :
    ((cappedCompositions M K : Finset (Fin K → ℕ)) : Set (Fin K → ℕ)).PairwiseDisjoint
      (compositionBlockFamily M) := by
  intro b hb c hc hbc
  apply blockFamily_disjoint_of_ne
  by_contra hnone
  push_neg at hnone
  apply hbc
  funext i
  simpa only [extendComposition_fin] using hnone i i.isLt

/-- The purely ordered-field calculation behind one vector class. -/
theorem cycleWeight_le_clusterQuotient
    {R T F P S W : ℝ}
    (hR : 0 ≤ R) (hT : 0 < T) (hF : 0 < F) (hP : 0 < P)
    (hS : 0 ≤ S) (hW : 0 < W)
    (hlower : R / F ≤ S) (hupper : F * W ≤ T * P) :
    (R ^ 2 / T) * (1 / (F * P)) ≤ S ^ 2 / W := by
  have hRF : 0 ≤ R / F := div_nonneg hR hF.le
  have hsquare : (R / F) ^ 2 ≤ S ^ 2 :=
    (sq_le_sq₀ hRF hS).2 hlower
  have hTP : 0 < T * P := mul_pos hT hP
  have hfrac0 : 0 ≤ (F * W) / (T * P) := by positivity
  have hfrac1 : (F * W) / (T * P) ≤ 1 :=
    (div_le_one hTP).2 hupper
  apply (le_div_iff₀ hW).2
  calc
    ((R ^ 2 / T) * (1 / (F * P))) * W =
        (R / F) ^ 2 * ((F * W) / (T * P)) := by
      field_simp [hT.ne', hF.ne', hP.ne', hW.ne']
    _ ≤ (R / F) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hfrac1 (sq_nonneg _)
    _ ≤ S ^ 2 := by simpa using hsquare

/-- Capped block classes, with their arithmetic estimates supplied as
hypotheses, contribute the full capped cyclic-weight sum to the density.

Subsequent files instantiate `R` and `T` by constant multiples of
`(2 * log 2)^K`; keeping the interface abstract makes every cancellation in
the analytic reduction explicit. -/
theorem cappedBlock_partitioned_lower
    {N y B M K : ℕ} {R T : ℝ}
    (hK : 0 < K)
    (hN : 3 ≤ N)
    (hy3 : 3 ≤ y)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
      dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ))
    (hy : 0 < y) (hBy : B ≤ 2 * y)
    (hbound : ∀ b ∈ cappedCompositions M K,
      ∀ a ∈ compositionBlockFamily M b, a ≤ B)
    (hBsq : B * B < y)
    (hscale : ∀ b ∈ cappedCompositions M K,
      ∀ a ∈ compositionBlockFamily M b, ∀ d ∈ a.divisors,
        N ≤ y / d ∧ y ≤ (y / d) ^ 2)
    (hR : 0 ≤ R) (hT : 0 < T)
    (hW : ∀ b ∈ cappedCompositions M K,
      0 < ∑ a ∈ compositionBlockFamily M b,
        (closePairCount a : ℝ) / a)
    (hlower : ∀ b ∈ cappedCompositions M K,
      R / compositionFactorial b ≤
        ∑ a ∈ compositionBlockFamily M b,
          (a.divisors.card : ℝ) / a)
    (hupper : ∀ b ∈ cappedCompositions M K,
      compositionFactorial b *
          (∑ a ∈ compositionBlockFamily M b,
            (closePairCount a : ℝ) / a) ≤
        T * compositionPenalty b) :
    smallPrimeEulerDensity (2 * y) *
        (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
          (R ^ 2 / T) *
          (∑ b ∈ cappedCompositions M K,
            compositionCycleWeight b)) ≤
      epsilon y (2 * y) := by
  let c : ℝ := (1 / 96 : ℝ) / Real.log (y : ℝ)
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpart := ford_partitioned_cluster_lower_reduction
    (I := cappedCompositions M K)
    (A := compositionBlockFamily M)
    hN hprime hy hBy (cappedBlockFamilies_pairwiseDisjoint M K)
    (fun _b _hb a ha ↦ blockFamily_pos ha)
    hbound hBsq
    (fun _b _hb a ha ↦ blockFamily_squarefree ha)
    hscale hW
  have hterm : ∀ b ∈ cappedCompositions M K,
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
    have hpen : 0 < compositionPenalty b := by
      exact compositionPenalty_pos_of_pos_length hK b
    have hS : 0 ≤ ∑ a ∈ compositionBlockFamily M b,
        (a.divisors.card : ℝ) / a := by
      apply Finset.sum_nonneg
      intro a ha
      exact div_nonneg (by positivity) (by positivity)
    have hq := cycleWeight_le_clusterQuotient hR hT hfac hpen hS
      (hW b hb) (hlower b hb) (hupper b hb)
    rw [compositionCycleWeight]
    calc
      c * (R ^ 2 / T) * (1 / (compositionFactorial b * compositionPenalty b)) =
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
          (∑ b ∈ cappedCompositions M K,
            compositionCycleWeight b)) =
        smallPrimeEulerDensity (2 * y) *
          (∑ b ∈ cappedCompositions M K,
            c * (R ^ 2 / T) * compositionCycleWeight b) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ smallPrimeEulerDensity (2 * y) *
        (∑ b ∈ cappedCompositions M K,
          (c *
              (∑ a ∈ compositionBlockFamily M b,
                (a.divisors.card : ℝ) / a) ^ 2) /
            (∑ a ∈ compositionBlockFamily M b,
              (closePairCount a : ℝ) / a)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum hterm
      · exact smallPrimeEulerDensity_nonneg _
    _ ≤ epsilon y (2 * y) := by simpa only [c] using hpart

end Erdos446
