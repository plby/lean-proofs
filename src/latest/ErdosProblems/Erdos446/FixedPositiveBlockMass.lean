/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.IsolatedBlockFamily

/-!
# Erdős Problem 446: Ford's positive squarefree block mass

This file packages the positive part of Ford's fixed-multiplicity
construction.  The diagonal-sharp reciprocal-prime estimates from
`SharpBlockMass` and `SharpBlockClose` show that every block-count vector
whose normalized close-pair factor is at most `13 / 10` contributes at least
one third of its ideal mass to `3 * tau - 2 * W`.  The classes are disjoint,
so they may be summed.  Finally the reciprocal-factorial sum is normalized
as the volume of the corresponding union of ordered multinomial boxes; this
is the fully finite form of (46), at the specialization `k = v` used in the
resolution of Problem 446.

The last section records the endpoint caps.  They ensure that every integer
in the family is squarefree, has exactly the prescribed number of prime
factors, lies below the chosen size endpoint, and has no prime factor below
the first block.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-! ## The good block-count vectors -/

/-- The vectors for which the sharp close-pair multiplier is at most
`13 / 10`.  Together with a one-percent lower-mass loss this leaves
`3 * (99 / 100) - 2 * (13 / 10) = 37 / 100 > 1 / 3`. -/
noncomputable def fordPositiveCompositions
    (M K : ℕ) (E : ℝ) : Finset (Fin K → ℕ) :=
  (cappedCompositions M K).filter fun b ↦
    Real.exp E *
      (1 + (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) *
        compositionPenalty b) ≤ 13 / 10

theorem mem_fordPositiveCompositions {M K : ℕ} {E : ℝ}
    {b : Fin K → ℕ} :
    b ∈ fordPositiveCompositions M K E ↔
      b ∈ cappedCompositions M K ∧
      Real.exp E *
        (1 + (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) *
          compositionPenalty b) ≤ 13 / 10 := by
  simp [fordPositiveCompositions]

/-- The disjoint union of the squarefree vector classes admitted above. -/
noncomputable def fordPositiveBlockFamily
    (M K : ℕ) (E : ℝ) : Finset ℕ :=
  (fordPositiveCompositions M K E).biUnion (compositionBlockFamily M)

theorem fordPositiveBlockFamilies_pairwiseDisjoint
    (M K : ℕ) (E : ℝ) :
    ((fordPositiveCompositions M K E : Finset (Fin K → ℕ)) :
      Set (Fin K → ℕ)).PairwiseDisjoint (compositionBlockFamily M) := by
  intro b hb c hc hbc
  exact cappedBlockFamilies_pairwiseDisjoint M K
    (mem_fordPositiveCompositions.mp hb).1
    (mem_fordPositiveCompositions.mp hc).1 hbc

/-! ## One vector and the summed positive defect -/

/-- A good vector supplies at least one third of its ideal reciprocal mass
to the positive close-pair defect.  This is the quantitative core of
Ford's estimate (43) specialized to the neighbourhood `sigma = log 2`. -/
theorem compositionBlockFamily_defect_lower_one_third
    {N M K : ℕ} {C E : ℝ}
    (hM : 1 ≤ M) (hK : 0 < K) (hC : 0 ≤ C)
    {b : Fin K → ℕ} (hb : b ∈ fordPositiveCompositions M K E)
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
    ((1 / 3 : ℝ) * (2 * Real.log 2 : ℝ) ^ K /
        compositionFactorial b) ≤
      ∑ a ∈ compositionBlockFamily M b,
        (3 * (2 : ℝ) ^ K -
          2 * (sigmaClosePairCount a (Real.log 2) : ℝ)) / (a : ℝ) := by
  have hbcap := (mem_fordPositiveCompositions.mp hb).1
  have hquality := (mem_fordPositiveCompositions.mp hb).2
  let Base : ℝ := (2 * Real.log 2 : ℝ) ^ K
  let S : ℝ := ∑ a ∈ compositionBlockFamily M b,
    (a.divisors.card : ℝ) / (a : ℝ)
  let W : ℝ := ∑ a ∈ compositionBlockFamily M b,
    (closePairCount a : ℝ) / (a : ℝ)
  let F : ℝ := compositionFactorial b
  have hBase0 : 0 ≤ Base := by dsimp [Base]; positivity
  have hF : 0 < F := by dsimp [F, compositionFactorial]; positivity
  have hmassLower : Base * (99 / 100 : ℝ) / F ≤ S := by
    have h := compositionBlockFamily_divisorMass_lower_sharp
      hM hC (by norm_num : (1 / 100 : ℝ) ≤ 1)
      hbcap hmass hselect hbudget
    simpa only [show (1 - (1 / 100 : ℝ)) = 99 / 100 by norm_num,
      Base, F, S] using h
  have hcloseMul : F * W ≤ Base * (13 / 10 : ℝ) := by
    have h := compositionBlockFamily_closeWeight_upper_sharp
      hM hK hC hbcap hmass hhalf hE hN hendpoint hprime
    calc
      F * W ≤ Base * Real.exp E *
          (1 + (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) *
            compositionPenalty b) := by simpa [F, W, Base] using h
      _ = Base * (Real.exp E *
          (1 + (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) *
            compositionPenalty b)) := by ring
      _ ≤ Base * (13 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hquality hBase0
  have hclose : W ≤ Base * (13 / 10 : ℝ) / F := by
    exact (le_div_iff₀ hF).2 (by simpa [mul_comm] using hcloseMul)
  rw [compositionBlockFamily_defect_eq hbcap]
  change (1 / 3 : ℝ) * Base / F ≤ 3 * S - 2 * W
  have hBaseDiv : 0 ≤ Base / F := div_nonneg hBase0 hF.le
  calc
    (1 / 3 : ℝ) * Base / F =
        (1 / 3 : ℝ) * (Base / F) := by ring
    _ ≤ (37 / 100 : ℝ) * (Base / F) :=
      mul_le_mul_of_nonneg_right (by norm_num) hBaseDiv
    _ = Base * (37 / 100 : ℝ) / F := by ring
    _ = 3 * (Base * (99 / 100 : ℝ) / F) -
        2 * (Base * (13 / 10 : ℝ) / F) := by ring
    _ ≤ 3 * S - 2 * W := by
      exact sub_le_sub
        (mul_le_mul_of_nonneg_left hmassLower (by norm_num))
        (mul_le_mul_of_nonneg_left hclose (by norm_num))

/-- Summed defect lower bound over all admitted vector classes. -/
theorem fordPositiveBlockFamily_defect_lower
    {N M K : ℕ} {C E : ℝ}
    (hM : 1 ≤ M) (hK : 0 < K) (hC : 0 ≤ C)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hselect : ∀ b ∈ fordPositiveCompositions M K E, ∀ i : Fin K,
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
    (1 / 3 : ℝ) * (2 * Real.log 2 : ℝ) ^ K *
        (∑ b ∈ fordPositiveCompositions M K E,
          1 / compositionFactorial b) ≤
      ∑ a ∈ fordPositiveBlockFamily M K E,
        (3 * (2 : ℝ) ^ K -
          2 * (sigmaClosePairCount a (Real.log 2) : ℝ)) / (a : ℝ) := by
  rw [fordPositiveBlockFamily,
    Finset.sum_biUnion (fordPositiveBlockFamilies_pairwiseDisjoint M K E)]
  calc
    (1 / 3 : ℝ) * (2 * Real.log 2 : ℝ) ^ K *
          (∑ b ∈ fordPositiveCompositions M K E,
            1 / compositionFactorial b) =
        ∑ b ∈ fordPositiveCompositions M K E,
          (1 / 3 : ℝ) * (2 * Real.log 2 : ℝ) ^ K /
            compositionFactorial b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b hb
      exact compositionBlockFamily_defect_lower_one_third
        hM hK hC hb hmass (hselect b hb) hbudget hhalf hE
        hN hendpoint hprime

/-! ## Multinomial boxes and the finite form of (46) -/

/-- Volume of the union of ordered multinomial boxes indexed by the good
vectors.  A vector `b` contributes exactly `1 / (K^K * prod b_i!)`. -/
noncomputable def fordPositiveBoxVolume (M K : ℕ) (E : ℝ) : ℝ :=
  ∑ b ∈ fordPositiveCompositions M K E,
    1 / ((K : ℝ) ^ K * compositionFactorial b)

theorem fordPositiveBoxVolume_nonneg (M K : ℕ) (E : ℝ) :
    0 ≤ fordPositiveBoxVolume M K E := by
  apply Finset.sum_nonneg
  intro b hb
  exact one_div_nonneg.mpr (mul_nonneg (pow_nonneg (Nat.cast_nonneg K) K)
    (le_of_lt (by dsimp [compositionFactorial]; positivity)))

theorem pow_mul_fordPositiveBoxVolume
    {M K : ℕ} {E : ℝ} (hK : 0 < K) :
    (K : ℝ) ^ K * fordPositiveBoxVolume M K E =
      ∑ b ∈ fordPositiveCompositions M K E,
        1 / compositionFactorial b := by
  rw [fordPositiveBoxVolume, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hKpow : (K : ℝ) ^ K ≠ 0 := pow_ne_zero _ hKR
  field_simp [hKpow]

/-- Ford's positive block-mass estimate (46), in its exact finite box form
at `k = v = K`. -/
theorem ford_positive_block_mass_46
    {N M K : ℕ} {C E : ℝ}
    (hM : 1 ≤ M) (hK : 0 < K) (hC : 0 ≤ C)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hselect : ∀ b ∈ fordPositiveCompositions M K E, ∀ i : Fin K,
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
    (1 / 3 : ℝ) * (2 * (K : ℝ) * Real.log 2) ^ K *
        fordPositiveBoxVolume M K E ≤
      ∑ a ∈ fordPositiveBlockFamily M K E,
        (3 * (2 : ℝ) ^ K -
          2 * (sigmaClosePairCount a (Real.log 2) : ℝ)) / (a : ℝ) := by
  have hdefect := fordPositiveBlockFamily_defect_lower
    hM hK hC hmass hselect hbudget hhalf hE hN hendpoint hprime
  rw [← pow_mul_fordPositiveBoxVolume (M := M) (E := E) hK] at hdefect
  convert hdefect using 1 <;> ring

/-- Combining (46) with Ford's isolated-divisor power inequality (41)
produces the exact extra factor `2^(K(r-1))` needed for a fixed
multiplicity `r`. -/
theorem ford_positive_block_isolated_power_mass
    {N M K r : ℕ} {C E : ℝ}
    (hM : 1 ≤ M) (hK : 0 < K) (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hselect : ∀ b ∈ fordPositiveCompositions M K E, ∀ i : Fin K,
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
    (((2 : ℝ) ^ K / 2) ^ (r - 1)) *
        ((1 / 6 : ℝ) * (2 * (K : ℝ) * Real.log 2) ^ K *
          fordPositiveBoxVolume M K E) ≤
      ∑ a ∈ fordPositiveBlockFamily M K E,
        ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) / (a : ℝ) := by
  have hdefect := ford_positive_block_mass_46
    hM hK hC hmass hselect hbudget hhalf hE hN hendpoint hprime
  have hmeta : ∀ a ∈ fordPositiveBlockFamily M K E,
      0 < a ∧ Squarefree a ∧ a.primeFactors.card = K := by
    intro a ha
    obtain ⟨b, hb, ha⟩ := Finset.mem_biUnion.mp ha
    exact compositionBlockFamily_squarefree_card
      (mem_fordPositiveCompositions.mp hb).1 ha
  have hisolated := isolatedPowerMass_lower_of_squarefree_defect
    (fordPositiveBlockFamily M K E) r K hmeta
    (Real.log_nonneg one_le_two) hr hdefect
  calc
    (((2 : ℝ) ^ K / 2) ^ (r - 1)) *
        ((1 / 6 : ℝ) * (2 * (K : ℝ) * Real.log 2) ^ K *
          fordPositiveBoxVolume M K E) =
      (((2 : ℝ) ^ K / 2) ^ (r - 1)) *
        (((1 / 3 : ℝ) * (2 * (K : ℝ) * Real.log 2) ^ K *
          fordPositiveBoxVolume M K E) / 2) := by ring
    _ ≤ _ := hisolated

/-! ## Endpoint caps and squarefree metadata -/

theorem compositionBlockFamily_primeFactor_gt_start
    {M K : ℕ} {b : Fin K → ℕ} {a p : ℕ}
    (ha : a ∈ compositionBlockFamily M b) (hp : p ∈ a.primeFactors) :
    blockEndpoint M < p := by
  obtain ⟨S, hS, rfl⟩ := mem_blockFamily.mp ha
  rw [selectionProduct_primeFactors hS] at hp
  obtain ⟨i, hi, hpBlock⟩ :=
    mem_blockPool.mp ((mem_blockSelectionSets.mp hS).1 hp)
  exact lt_of_le_of_lt (blockEndpoint_mono (Nat.le_add_right M i))
    (mem_primeBlock.mp hpBlock).2.1

theorem compositionBlockFamily_le_endpoint_pow
    {M K : ℕ} {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K)
    {a : ℕ} (ha : a ∈ compositionBlockFamily M b) :
    a ≤ blockEndpoint (M + K) ^ K := by
  obtain ⟨S, hS, hprod⟩ := mem_blockFamily.mp ha
  have hSCard : S.card = K := by
    rw [card_selection_eq_sum hS, sum_range_extendComposition b]
    exact mem_compositions.mp (mem_cappedCompositions.mp hb).1
  have hpBound : ∀ p ∈ S, p ≤ blockEndpoint (M + K) := by
    intro p hp
    obtain ⟨i, hi, hpBlock⟩ :=
      mem_blockPool.mp ((mem_blockSelectionSets.mp hS).1 hp)
    exact (mem_primeBlock.mp hpBlock).2.2.trans
      (blockEndpoint_mono (by omega))
  have hprodLe := Finset.prod_le_pow_card S id (blockEndpoint (M + K)) hpBound
  rw [hSCard] at hprodLe
  rw [← hprod]
  exact hprodLe

/-- Every member of the positive family obeys all arithmetic conditions
required in (46): positivity, squarefreeness, exactly `K` prime factors,
the upper size cap, and the lower prime-factor cap. -/
theorem fordPositiveBlockFamily_endpoint_caps
    {M K B : ℕ} {E : ℝ}
    (hB : blockEndpoint (M + K) ^ K ≤ B)
    {a : ℕ} (ha : a ∈ fordPositiveBlockFamily M K E) :
    0 < a ∧ Squarefree a ∧ a.primeFactors.card = K ∧ a ≤ B ∧
      ∀ p ∈ a.primeFactors, blockEndpoint M < p := by
  obtain ⟨b, hb, ha⟩ := Finset.mem_biUnion.mp ha
  have hbcap := (mem_fordPositiveCompositions.mp hb).1
  have hmeta := compositionBlockFamily_squarefree_card hbcap ha
  refine ⟨hmeta.1, hmeta.2.1, hmeta.2.2,
    (compositionBlockFamily_le_endpoint_pow hbcap ha).trans hB, ?_⟩
  intro p hp
  exact compositionBlockFamily_primeFactor_gt_start ha hp

/-- Real form of the lower endpoint cap: choosing the first block above
`exp sigma` makes every prime factor exceed `exp sigma`. -/
theorem fordPositiveBlockFamily_primeFactors_gt_exp
    {M K : ℕ} {E sigma : ℝ}
    (hsigma : Real.exp sigma < (blockEndpoint M : ℝ))
    {a : ℕ} (ha : a ∈ fordPositiveBlockFamily M K E) :
    ∀ p ∈ a.primeFactors, Real.exp sigma < (p : ℝ) := by
  intro p hp
  have hpNat : blockEndpoint M < p := by
    obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp ha
    exact compositionBlockFamily_primeFactor_gt_start hab hp
  exact hsigma.trans (by exact_mod_cast hpNat)

end Erdos446
