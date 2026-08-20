/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedLowerCaps
import ErdosProblems.Erdos446.FixedLowerEnergyMoment
import ErdosProblems.Erdos446.FixedLowerSizeRetention
import ErdosProblems.Erdos446.SizedBlockBounds

/-!
# Erdős Problem 446: the size-truncated positive isolated family

Ford's fixed-multiplicity family needs three simultaneous restrictions on a
block-count vector: the one-slack Smirnov barrier, the prefix-energy cutoff,
and the product-size cutoff.  This file defines that final finite family and
the corresponding size-truncated positive prime-block family.

The size cutoff is the one already used by `sizedCappedCompositions`, namely
`compositionSizeCost c ≤ 16 * 2^k`.  Hence every integer represented by the
resulting block family is bounded by `fordConstructionBound M k`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-! ## Fully restricted occupancies -/

/-- One-slack occupancies surviving both the energy cutoff and the product
size cutoff.  Ford's pointwise block caps are already included in
`fixedLowerRestrictedOccupancies`. -/
noncomputable def fixedLowerSizedOccupancies
    (M k : ℕ) (T : ℝ) : Finset (Fin k → ℕ) :=
  (fixedLowerRestrictedOccupancies M k T).filter fun c ↦
    compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k

theorem mem_fixedLowerSizedOccupancies
    {M k : ℕ} {T : ℝ} {c : Fin k → ℕ} :
    c ∈ fixedLowerSizedOccupancies M k T ↔
      c ∈ smirnovOccupancies k 1 k ∧
      fixedLowerPrefixEnergy c ≤ T ∧ IsFordCapped M c ∧
      compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k := by
  simp [fixedLowerSizedOccupancies,
    mem_fixedLowerRestrictedOccupancies, and_assoc]

noncomputable def fixedLowerSizedMass
    (M k : ℕ) (T : ℝ) : ℝ :=
  ∑ c ∈ fixedLowerSizedOccupancies M k T,
    1 / compositionFactorial c

/-- On the one-slack family Ford's forward cap is automatic, so the final
size-restricted set is exactly the energy-and-size set used by the two
independent Markov estimates. -/
theorem fixedLowerSizedOccupancies_eq_sizedEnergy
    {M k : ℕ} (hM : 1 ≤ M) (T : ℝ) :
    fixedLowerSizedOccupancies M k T =
      fixedLowerSizedEnergyOccupancies k T := by
  ext c
  rw [mem_fixedLowerSizedOccupancies,
    mem_fixedLowerSizedEnergyOccupancies]
  constructor
  · intro hc
    exact ⟨hc.1, hc.2.1, hc.2.2.2⟩
  · intro hc
    exact ⟨hc.1, hc.2.1,
      smirnovOccupancy_one_isFordCapped hM hc.1, hc.2.2⟩

theorem fixedLowerSizedMass_eq_sizedEnergy
    {M k : ℕ} (hM : 1 ≤ M) (T : ℝ) :
    fixedLowerSizedMass M k T = fixedLowerSizedEnergyMass k T := by
  rw [fixedLowerSizedMass, fixedLowerSizedEnergyMass,
    fixedLowerSizedOccupancies_eq_sizedEnergy hM T]

theorem fixedLowerSizedOccupancies_eq_sizedRestricted
    (M k : ℕ) (T : ℝ) :
    fixedLowerSizedOccupancies M k T =
      fixedLowerSizedRestrictedOccupancies M k T := by
  rfl

theorem fixedLowerSizedMass_eq_sizedRestricted
    (M k : ℕ) (T : ℝ) :
    fixedLowerSizedMass M k T =
      fixedLowerSizedRestrictedMass M k T := by
  rfl

/-- Closed two-cutoff Markov theorem for the final family.  It can be
instantiated directly with any proved uniform prefix-energy moment bound.
-/
theorem fixedLowerSizedMass_eighth_scale_of_moment
    {M k : ℕ} (hM : 1 ≤ M) (hk : 2 ≤ k)
    {C : ℝ} (hC : 0 < C)
    (hmoment : fixedLowerPrefixEnergyMoment k ≤
      C * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ))) :
    (1 / 8 : ℝ) *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
      fixedLowerSizedMass M k (2 * C) := by
  rw [fixedLowerSizedMass_eq_sizedRestricted]
  exact fixedLowerSizedRestrictedMass_eighth_scale_of_moments
    hM hk hC hmoment

/-- Unconditional fixed-fraction lower mass at the absolute energy cutoff
obtained from the proved uniform prefix-energy moment estimate. -/
theorem fixedLowerSizedMass_eighth_scale
    {M k : ℕ} (hM : 1 ≤ M) (hk : 2 ≤ k) :
    (1 / 8 : ℝ) *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
      fixedLowerSizedMass M k (16000 * Real.exp 4) := by
  have h := fixedLowerSizedMass_eighth_scale_of_moment
    hM hk (C := 8000 * Real.exp 4) (by positivity)
      (fixedLowerPrefixEnergyMoment_le_scale (by omega))
  convert h using 1 <;> ring

/-- The simultaneous finite Markov bound, stated directly for the final
restricted family.  The last term is the exact loss supplied by the
weighted-size first moment. -/
theorem fixedLowerSizedMass_lower_of_moment
    {M k : ℕ} (hM : 1 ≤ M) (hk : 2 ≤ k)
    {T L A : ℝ} (hT : 0 < T)
    (hmass : L ≤ smirnovOccupancyMass k 1 k)
    (hmoment : fixedLowerPrefixEnergyMoment k ≤ A) :
    L - A / T - smirnovOccupancyMass k 1 k / 8 ≤
      fixedLowerSizedMass M k T := by
  rw [fixedLowerSizedMass_eq_sizedEnergy hM T]
  exact fixedLowerSizedEnergyMass_lower hk hT hmass hmoment

/-! ## Size-truncated positive block families -/

/-- Positive isolated compositions with the additional product-size
cutoff required by the exact-multiplicity construction. -/
noncomputable def positiveSizedIsolatedCompositions
    (M k : ℕ) (E : ℝ) : Finset (Fin k → ℕ) :=
  (positiveIsolatedCompositions M k E).filter fun c ↦
    compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k

theorem mem_positiveSizedIsolatedCompositions
    {M k : ℕ} {E : ℝ} {c : Fin k → ℕ} :
    c ∈ positiveSizedIsolatedCompositions M k E ↔
      c ∈ positiveIsolatedCompositions M k E ∧
      compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k := by
  simp [positiveSizedIsolatedCompositions]

noncomputable def positiveSizedIsolatedBlockFamily
    (M k : ℕ) (E : ℝ) : Finset ℕ :=
  (positiveSizedIsolatedCompositions M k E).biUnion
    (compositionBlockFamily M)

theorem positiveSizedIsolatedBlockFamilies_pairwiseDisjoint
    (M k : ℕ) (E : ℝ) :
    ((positiveSizedIsolatedCompositions M k E : Finset (Fin k → ℕ)) :
      Set (Fin k → ℕ)).PairwiseDisjoint (compositionBlockFamily M) := by
  intro b hb c hc hbc
  exact positiveIsolatedBlockFamilies_pairwiseDisjoint M k E
    (mem_positiveSizedIsolatedCompositions.mp hb).1
    (mem_positiveSizedIsolatedCompositions.mp hc).1 hbc

/-- Every member of the size-truncated family is positive, squarefree, has
exactly `k` prime factors, and lies below Ford's construction bound. -/
theorem positiveSizedIsolatedBlockFamily_metadata
    {M k : ℕ} {E : ℝ} {a : ℕ}
    (ha : a ∈ positiveSizedIsolatedBlockFamily M k E) :
    0 < a ∧ Squarefree a ∧ a.primeFactors.card = k ∧
      a ≤ fordConstructionBound M k := by
  obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
  have hcData := mem_positiveSizedIsolatedCompositions.mp hc
  have hcPos := mem_positiveIsolatedCompositions.mp hcData.1
  have hcSized : c ∈ sizedCappedCompositions M k := by
    rw [mem_sizedCappedCompositions]
    exact ⟨hcPos.1, hcData.2⟩
  have hmeta := compositionBlockFamily_squarefree_card hcPos.1 hac
  exact ⟨hmeta.1, hmeta.2.1, hmeta.2.2,
    sizedBlockFamily_le_constructionBound hcSized hac⟩

/-- The fully restricted occupancy family is contained in the concrete
size-truncated positive family as soon as the numerical close-pair factor
is valid at the cutoff `T`. -/
theorem fixedLowerSizedOccupancies_subset_positiveSized
    {M k : ℕ} {T E Q : ℝ} (hQ : 0 ≤ Q)
    (hquality : Real.exp E * (1 + Q * T) ≤ 4 / 3)
    (hQdef : Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) :
    fixedLowerSizedOccupancies M k T ⊆
      positiveSizedIsolatedCompositions M k E := by
  intro c hc
  have hcData := mem_fixedLowerSizedOccupancies.mp hc
  rw [mem_positiveSizedIsolatedCompositions]
  refine ⟨fixedLowerRestrictedOccupancies_subset_positiveIsolated
    hQ hquality hQdef ?_, hcData.2.2.2⟩
  exact mem_fixedLowerRestrictedOccupancies.mpr
    ⟨hcData.1, hcData.2.1, hcData.2.2.1⟩

/-- A reciprocal-factorial lower bound for the fully restricted family
therefore transfers directly to the size-truncated positive family. -/
theorem positiveSizedIsolatedCompositions_mass_lower_of_fixedLower
    {M k : ℕ} {T E Q B : ℝ} (hQ : 0 ≤ Q)
    (hquality : Real.exp E * (1 + Q * T) ≤ 4 / 3)
    (hQdef : Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M))
    (hB : B ≤ fixedLowerSizedMass M k T) :
    B ≤ ∑ c ∈ positiveSizedIsolatedCompositions M k E,
      1 / compositionFactorial c := by
  exact hB.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (fixedLowerSizedOccupancies_subset_positiveSized hQ hquality hQdef)
    (fun c hc _ ↦ inv_compositionFactorial_nonneg' c))

/-- The two finite Markov truncations feed directly into the concrete
size-truncated positive family. -/
theorem positiveSizedIsolatedCompositions_mass_eighth_scale_of_moment
    {M k : ℕ} {C E Q : ℝ}
    (hM : 1 ≤ M) (hk : 2 ≤ k) (hC : 0 < C)
    (hmoment : fixedLowerPrefixEnergyMoment k ≤
      C * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)))
    (hQ : 0 ≤ Q)
    (hquality : Real.exp E * (1 + Q * (2 * C)) ≤ 4 / 3)
    (hQdef : Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) :
    (1 / 8 : ℝ) *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
      ∑ c ∈ positiveSizedIsolatedCompositions M k E,
        1 / compositionFactorial c := by
  apply positiveSizedIsolatedCompositions_mass_lower_of_fixedLower
    hQ hquality hQdef
  exact fixedLowerSizedMass_eighth_scale_of_moment
    hM hk hC hmoment

/-- The final composition theorem: after the energy and product-size
truncations, the concrete positive isolated family retains at least one
eighth of Ford's natural reciprocal-factorial mass.  Its only remaining
hypotheses are the numerical prime-block quality conditions later supplied
by the fixed-multiplicity parameter choice. -/
theorem positiveSizedIsolatedCompositions_mass_eighth_scale
    {M k : ℕ} {E Q : ℝ}
    (hM : 1 ≤ M) (hk : 2 ≤ k) (hQ : 0 ≤ Q)
    (hquality :
      Real.exp E * (1 + Q * (16000 * Real.exp 4)) ≤ 4 / 3)
    (hQdef : Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) :
    (1 / 8 : ℝ) *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
      ∑ c ∈ positiveSizedIsolatedCompositions M k E,
        1 / compositionFactorial c := by
  apply positiveSizedIsolatedCompositions_mass_eighth_scale_of_moment
    (C := 8000 * Real.exp 4) hM hk (by positivity)
    (fixedLowerPrefixEnergyMoment_le_scale (by omega)) hQ
  · convert hquality using 1 <;> ring
  · exact hQdef

/-! ## Isolated-divisor mass on the size-truncated family -/

/-- Summing the already proved one-vector isolated-divisor inequality over
the size-truncated subfamily preserves the full fixed-`r` factor. -/
theorem positiveSizedIsolatedBlockFamily_isolatedPowerMass_lower
    {N M k r : ℕ} {C E : ℝ}
    (hM : 1 ≤ M) (hk : 0 < k) (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hmass : ∀ i : Fin k,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hselect : ∀ b ∈ positiveSizedIsolatedCompositions M k E,
      ∀ i : Fin k,
        (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
          primeBlockMass (M + i))
    (hbudget :
      (4 * (M * M) * C + 12 * (M * M) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ M) ≤ 1 / 100)
    (hhalf : ∀ i : Fin k,
      Real.log 2 / 2 ≤ primeBlockMass (M + i))
    (hE : 4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ E)
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin k,
      N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ)) :
    ((((2 : ℝ) ^ k) / 2) ^ (r - 1)) * (91 / 600 : ℝ) *
        (2 * Real.log 2 : ℝ) ^ k *
        (∑ b ∈ positiveSizedIsolatedCompositions M k E,
          1 / compositionFactorial b) ≤
      ∑ a ∈ positiveSizedIsolatedBlockFamily M k E,
        ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) / (a : ℝ) := by
  rw [positiveSizedIsolatedBlockFamily,
    Finset.sum_biUnion
      (positiveSizedIsolatedBlockFamilies_pairwiseDisjoint M k E)]
  calc
    (((2 : ℝ) ^ k / 2) ^ (r - 1)) * (91 / 600 : ℝ) *
          (2 * Real.log 2 : ℝ) ^ k *
          (∑ b ∈ positiveSizedIsolatedCompositions M k E,
            1 / compositionFactorial b) =
        ∑ b ∈ positiveSizedIsolatedCompositions M k E,
          (((2 : ℝ) ^ k / 2) ^ (r - 1)) *
            ((91 / 600 : ℝ) *
              ((2 * Real.log 2 : ℝ) ^ k /
                compositionFactorial b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b hb
      exact compositionBlockFamily_isolatedPowerMass_lower
        hM hk hC hr (mem_positiveSizedIsolatedCompositions.mp hb).1
        hmass (hselect b hb) hbudget hhalf hE hN hendpoint hprime

end Erdos446
