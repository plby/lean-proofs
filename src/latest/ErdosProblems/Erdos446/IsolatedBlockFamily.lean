/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.IsolatedDivisorMass
import ErdosProblems.Erdos446.SharpBlockMass
import ErdosProblems.Erdos446.SharpBlockClose

/-!
# Erdős Problem 446: an isolated squarefree prime-block family

This file combines the diagonal-sharp block estimates with Ford's
isolated-divisor inequality.  It gives a concrete family of squarefree
integers, selected by an explicit numerical close-pair condition, whose
`r`th isolated-divisor reciprocal mass has the extra factor
`2^(K(r-1))` required by the fixed-multiplicity argument.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem sigmaClosePairCount_log_two (a : ℕ) :
    sigmaClosePairCount a (Real.log 2) = closePairCount a := by
  rfl

/-- Every member of a capped composition block family is squarefree and
has exactly `K` distinct prime factors. -/
theorem compositionBlockFamily_squarefree_card
    {M K : ℕ} {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K)
    {a : ℕ} (ha : a ∈ compositionBlockFamily M b) :
    0 < a ∧ Squarefree a ∧ a.primeFactors.card = K := by
  refine ⟨blockFamily_pos ha, blockFamily_squarefree ha, ?_⟩
  obtain ⟨S, hS, hprod⟩ := mem_blockFamily.mp ha
  rw [← hprod, selectionProduct_primeFactors hS, card_selection_eq_sum hS,
    sum_range_extendComposition b]
  exact mem_compositions.mp (mem_cappedCompositions.mp hb).1

/-- The reciprocal close-pair defect of one composition family is the
difference between three copies of its divisor mass and two copies of its
close-pair mass. -/
theorem compositionBlockFamily_defect_eq
    {M K : ℕ} {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K) :
    (∑ a ∈ compositionBlockFamily M b,
        (3 * (2 : ℝ) ^ K -
          2 * (sigmaClosePairCount a (Real.log 2) : ℝ)) / (a : ℝ)) =
      3 * (∑ a ∈ compositionBlockFamily M b,
        (a.divisors.card : ℝ) / (a : ℝ)) -
      2 * (∑ a ∈ compositionBlockFamily M b,
        (closePairCount a : ℝ) / (a : ℝ)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hcard := blockFamily_divisors_card ha
  rw [sum_range_extendComposition b,
    mem_compositions.mp (mem_cappedCompositions.mp hb).1] at hcard
  rw [sigmaClosePairCount_log_two, hcard]
  push_cast
  ring

/-- Explicitly good capped vectors: the sharp close-pair upper bound is at
most `4/3` times the ideal block mass. -/
noncomputable def positiveIsolatedCompositions
    (M K : ℕ) (E : ℝ) : Finset (Fin K → ℕ) :=
  (cappedCompositions M K).filter fun b ↦
    Real.exp E *
      (1 + (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) *
        compositionPenalty b) ≤ 4 / 3

theorem mem_positiveIsolatedCompositions {M K : ℕ} {E : ℝ}
    {b : Fin K → ℕ} :
    b ∈ positiveIsolatedCompositions M K E ↔
      b ∈ cappedCompositions M K ∧
      Real.exp E *
        (1 + (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) *
          compositionPenalty b) ≤ 4 / 3 := by
  simp [positiveIsolatedCompositions]

/-- Union of the mutually disjoint good vector classes. -/
noncomputable def positiveIsolatedBlockFamily
    (M K : ℕ) (E : ℝ) : Finset ℕ :=
  (positiveIsolatedCompositions M K E).biUnion
    (compositionBlockFamily M)

/-- The concrete union family consists entirely of positive squarefree
integers with `K` distinct prime factors. -/
theorem positiveIsolatedBlockFamily_squarefree_card
    {M K : ℕ} {E : ℝ} {a : ℕ}
    (ha : a ∈ positiveIsolatedBlockFamily M K E) :
    0 < a ∧ Squarefree a ∧ a.primeFactors.card = K := by
  obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp ha
  exact compositionBlockFamily_squarefree_card
    (mem_positiveIsolatedCompositions.mp hb).1 hab

theorem positiveIsolatedBlockFamilies_pairwiseDisjoint
    (M K : ℕ) (E : ℝ) :
    ((positiveIsolatedCompositions M K E : Finset (Fin K → ℕ)) :
      Set (Fin K → ℕ)).PairwiseDisjoint (compositionBlockFamily M) := by
  intro b hb c hc hbc
  exact cappedBlockFamilies_pairwiseDisjoint M K
    (mem_positiveIsolatedCompositions.mp hb).1
    (mem_positiveIsolatedCompositions.mp hc).1 hbc

/-- One good prime-block class supplies the full fixed-`r` isolated-divisor
factor.  The numerical constant `91/600` is
`(3*(1-1/100)-2*(4/3))/2`. -/
theorem compositionBlockFamily_isolatedPowerMass_lower
    {N M K r : ℕ} {C E : ℝ}
    (hM : 1 ≤ M) (hK : 0 < K) (hC : 0 ≤ C) (hr : 1 ≤ r)
    {b : Fin K → ℕ} (hb : b ∈ positiveIsolatedCompositions M K E)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hselect : ∀ i : Fin K,
      (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
        primeBlockMass (M + i))
    (hbudget :
      (4 * (M * M) * C + 12 * (M * M) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ M) ≤ 1 / 100)
    (hhalf : ∀ i : Fin K,
      Real.log 2 / 2 ≤ primeBlockMass (M + i))
    (hE : 4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ E)
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin K, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ)) :
    ((((2 : ℝ) ^ K) / 2) ^ (r - 1)) *
        ((91 / 600 : ℝ) *
          ((2 * Real.log 2 : ℝ) ^ K / compositionFactorial b)) ≤
      ∑ a ∈ compositionBlockFamily M b,
        ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) / (a : ℝ) := by
  have hbcap := (mem_positiveIsolatedCompositions.mp hb).1
  have hquality := (mem_positiveIsolatedCompositions.mp hb).2
  let Base : ℝ := (2 * Real.log 2 : ℝ) ^ K
  let S : ℝ := ∑ a ∈ compositionBlockFamily M b,
    (a.divisors.card : ℝ) / (a : ℝ)
  let W : ℝ := ∑ a ∈ compositionBlockFamily M b,
    (closePairCount a : ℝ) / (a : ℝ)
  let F : ℝ := compositionFactorial b
  have hF : 0 < F := by dsimp [F, compositionFactorial]; positivity
  have hmassLower : Base * (99 / 100 : ℝ) / F ≤ S := by
    have h := compositionBlockFamily_divisorMass_lower_sharp
      hM hC (by norm_num : (1 / 100 : ℝ) ≤ 1)
      hbcap hmass hselect hbudget
    simpa only [show (1 - (1 / 100 : ℝ)) = 99 / 100 by norm_num,
      Base, F, S] using h
  have hcloseMul : F * W ≤ Base * (4 / 3 : ℝ) := by
    have h := compositionBlockFamily_closeWeight_upper_sharp
      hM hK hC hbcap hmass hhalf hE hN hendpoint hprime
    calc
      F * W ≤ Base * Real.exp E *
          (1 + (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) *
            compositionPenalty b) := by simpa [F, W, Base] using h
      _ = Base * (Real.exp E *
          (1 + (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) *
            compositionPenalty b)) := by ring
      _ ≤ Base * (4 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hquality (by dsimp [Base]; positivity)
  have hclose : W ≤ Base * (4 / 3 : ℝ) / F := by
    exact (le_div_iff₀ hF).2 (by simpa [mul_comm] using hcloseMul)
  have hdefect :
      Base * (91 / 300 : ℝ) / F ≤
        ∑ a ∈ compositionBlockFamily M b,
          (3 * (2 : ℝ) ^ K -
            2 * (sigmaClosePairCount a (Real.log 2) : ℝ)) / (a : ℝ) := by
    rw [compositionBlockFamily_defect_eq hbcap]
    change Base * (91 / 300 : ℝ) / F ≤ 3 * S - 2 * W
    calc
      Base * (91 / 300 : ℝ) / F =
          3 * (Base * (99 / 100 : ℝ) / F) -
            2 * (Base * (4 / 3 : ℝ) / F) := by ring
      _ ≤ 3 * S - 2 * W := by
        exact sub_le_sub
          (mul_le_mul_of_nonneg_left hmassLower (by norm_num))
          (mul_le_mul_of_nonneg_left hclose (by norm_num))
  have hisolated := isolatedPowerMass_lower_of_squarefree_defect
    (compositionBlockFamily M b) r K
    (fun a ha ↦ compositionBlockFamily_squarefree_card hbcap ha)
    (Real.log_nonneg one_le_two) hr hdefect
  calc
    (((2 : ℝ) ^ K / 2) ^ (r - 1)) *
        ((91 / 600 : ℝ) * (Base / F)) =
      (((2 : ℝ) ^ K / 2) ^ (r - 1)) *
        ((Base * (91 / 300 : ℝ) / F) / 2) := by ring
    _ ≤ _ := hisolated

/-- Summing the preceding bound over the disjoint good vector classes gives
a genuine squarefree family lower bound, not an abstract reduction
hypothesis. -/
theorem positiveIsolatedBlockFamily_isolatedPowerMass_lower
    {N M K r : ℕ} {C E : ℝ}
    (hM : 1 ≤ M) (hK : 0 < K) (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hselect : ∀ b ∈ positiveIsolatedCompositions M K E, ∀ i : Fin K,
      (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
        primeBlockMass (M + i))
    (hbudget :
      (4 * (M * M) * C + 12 * (M * M) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ M) ≤ 1 / 100)
    (hhalf : ∀ i : Fin K,
      Real.log 2 / 2 ≤ primeBlockMass (M + i))
    (hE : 4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ E)
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin K, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ)) :
    ((((2 : ℝ) ^ K) / 2) ^ (r - 1)) * (91 / 600 : ℝ) *
        (2 * Real.log 2 : ℝ) ^ K *
        (∑ b ∈ positiveIsolatedCompositions M K E,
          1 / compositionFactorial b) ≤
      ∑ a ∈ positiveIsolatedBlockFamily M K E,
        ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) / (a : ℝ) := by
  rw [positiveIsolatedBlockFamily,
    Finset.sum_biUnion (positiveIsolatedBlockFamilies_pairwiseDisjoint M K E)]
  calc
    (((2 : ℝ) ^ K / 2) ^ (r - 1)) * (91 / 600 : ℝ) *
          (2 * Real.log 2 : ℝ) ^ K *
          (∑ b ∈ positiveIsolatedCompositions M K E,
            1 / compositionFactorial b) =
        ∑ b ∈ positiveIsolatedCompositions M K E,
          (((2 : ℝ) ^ K / 2) ^ (r - 1)) *
            ((91 / 600 : ℝ) *
              ((2 * Real.log 2 : ℝ) ^ K /
                compositionFactorial b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b hb
      exact compositionBlockFamily_isolatedPowerMass_lower
        hM hK hC hr hb hmass (hselect b hb) hbudget hhalf hE
        hN hendpoint hprime

end Erdos446
