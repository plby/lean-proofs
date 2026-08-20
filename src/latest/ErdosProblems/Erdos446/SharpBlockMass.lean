/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.BlockMassBounds

/-!
# Erdős Problem 446: sharp retained mass in a block family

The dyadic lower bound only needs to retain one half of the ideal reciprocal
mass.  Ford's prescribed-multiplicity argument needs the sharper fact that an
arbitrary explicit loss budget `θ` retains the factor `1 - θ`.  This file
records that consequence of the already formalized falling-mass product.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- If the total Mertens and without-replacement loss is at most `θ ≤ 1`,
then the block family retains `1 - θ` of its ideal divisor mass. -/
theorem compositionBlockFamily_divisorMass_lower_sharp
    {M K : ℕ} {C θ : ℝ} (hM : 1 ≤ M) (hC : 0 ≤ C)
    (hθ1 : θ ≤ 1)
    {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hselect : ∀ i : Fin K,
      (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
        primeBlockMass (M + i))
    (hbudget :
      (4 * (M * M) * C + 12 * (M * M) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ M) ≤ θ) :
    (((2 * Real.log 2 : ℝ) ^ K * (1 - θ)) /
        compositionFactorial b) ≤
      ∑ a ∈ compositionBlockFamily M b,
        (a.divisors.card : ℝ) / a := by
  let z : BlockSlot K (extendComposition b) → ℝ :=
    blockSlotLoss C M b
  have hcap : ∀ i : Fin K,
      extendComposition b i ≤ (M * M) * (i.val + 1) :=
    cappedComposition_linear_cap hM hb
  have hz0 : ∀ s, 0 ≤ z s :=
    fun s ↦ blockSlotLoss_nonneg hC M b s
  have hzsum : (∑ s, z s) ≤ θ :=
    (blockSlotLoss_sum_le hC hcap).trans hbudget
  have hz1 : ∀ s, z s ≤ 1 := by
    intro s
    have hsle : z s ≤ ∑ t, z t :=
      Finset.single_le_sum (fun t _ht ↦ hz0 t) (Finset.mem_univ s)
    exact hsle.trans (hzsum.trans hθ1)
  have hfactor : ∀ s,
      Real.log 2 * (1 - z s) ≤
        primeBlockMass (M + s.1) -
          (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ) :=
    blockSlot_factor_lower hC hmass
  have hprod := prod_lower_of_relative_error
    (ι := BlockSlot K (extendComposition b))
    (Real.log 2) (Real.log_pos one_lt_two).le
    (fun s ↦ primeBlockMass (M + s.1) -
      (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ))
    z hz0 hz1 hfactor
  rw [card_blockSlot_extendComposition_of_mem hb] at hprod
  have hremain : 1 - θ ≤ 1 - ∑ s, z s := by linarith
  have hlogpow : 0 ≤ Real.log 2 ^ K := by positivity
  have hraw :
      Real.log 2 ^ K * (1 - θ) ≤
        ∏ s : BlockSlot K (extendComposition b),
          (primeBlockMass (M + s.1) -
            (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ)) := by
    calc
      Real.log 2 ^ K * (1 - θ) ≤
          Real.log 2 ^ K * (1 - ∑ s, z s) :=
        mul_le_mul_of_nonneg_left hremain hlogpow
      _ ≤ _ := hprod
  have hrecip := blockFamily_reciprocal_sum_falling_lower
    (M := M) (k := K) (b := extendComposition b)
    (by simpa only [extendComposition_fin] using hselect)
  simp only [extendComposition_fin] at hrecip
  have hnumerator :
      (∏ i : Fin K,
          ∏ t ∈ Finset.range (b i),
            (primeBlockMass (M + i) -
              (t : ℝ) / (blockEndpoint (M + i) : ℝ))) =
        ∏ s : BlockSlot K (extendComposition b),
          (primeBlockMass (M + s.1) -
            (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ)) := by
    have hslots := prod_blockSlot_local
      (k := K) (b := extendComposition b)
      (fun (i : Fin K) (t : Fin (extendComposition b i)) ↦
        primeBlockMass (M + i) -
          (t.val : ℝ) / (blockEndpoint (M + i) : ℝ))
    calc
      (∏ i : Fin K,
          ∏ t ∈ Finset.range (b i),
            (primeBlockMass (M + i) -
              (t : ℝ) / (blockEndpoint (M + i) : ℝ))) =
          ∏ i : Fin K, ∏ t : Fin (extendComposition b i),
            (primeBlockMass (M + i) -
              (t.val : ℝ) / (blockEndpoint (M + i) : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i hi
        simpa only [extendComposition_fin] using
          (Fin.prod_univ_eq_prod_range
            (fun t : ℕ ↦ primeBlockMass (M + i) -
              (t : ℝ) / (blockEndpoint (M + i) : ℝ))
            (extendComposition b i)).symm
      _ = _ := hslots.symm
  have hnested :
      (∏ i : Fin K,
          (∏ t ∈ Finset.range (b i),
            (primeBlockMass (M + i) -
              (t : ℝ) / (blockEndpoint (M + i) : ℝ))) /
            ((b i).factorial : ℝ)) =
        (∏ s : BlockSlot K (extendComposition b),
          (primeBlockMass (M + s.1) -
            (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ))) /
          compositionFactorial b := by
    rw [Finset.prod_div_distrib, hnumerator]
    rfl
  rw [hnested] at hrecip
  rw [compositionBlockFamily_divisorMass_eq hb]
  have hfac : 0 < compositionFactorial b := by
    dsimp [compositionFactorial]
    positivity
  have hrawDiv := div_le_div_of_nonneg_right hraw hfac.le
  calc
    ((2 * Real.log 2 : ℝ) ^ K * (1 - θ)) /
          compositionFactorial b =
        (2 : ℝ) ^ K *
          ((Real.log 2 ^ K * (1 - θ)) /
            compositionFactorial b) := by
      rw [mul_pow]
      ring
    _ ≤ (2 : ℝ) ^ K *
          ((∏ s : BlockSlot K (extendComposition b),
            (primeBlockMass (M + s.1) -
              (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ))) /
            compositionFactorial b) :=
      mul_le_mul_of_nonneg_left hrawDiv (by positivity)
    _ ≤ (2 : ℝ) ^ K *
          (∑ a ∈ blockFamily M K (extendComposition b), 1 / (a : ℝ)) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = (2 : ℝ) ^ K *
          ∏ i : Fin K, blockElementaryMass (M + i) (b i) := by
      rw [blockFamily_reciprocal_sum_factorization]
      simp only [extendComposition_fin]

end Erdos446
