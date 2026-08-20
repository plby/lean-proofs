/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedLowerSizeMoment
import ErdosProblems.Erdos446.FixedLowerReverseSize
import ErdosProblems.Erdos446.FixedPositiveBlockMass
import ErdosProblems.Erdos446.SizedBlockBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Erdős Problem 446: retaining mass after the size cutoff

The close-pair cutoff and the endpoint caps used in the fixed-multiplicity
argument do not by themselves bound the product of the selected primes.  We
therefore impose the same weighted-size cutoff as `sizedCappedCompositions`.
The first moment from `FixedLowerSizeMoment` shows that this deletes at most
one eighth of the complete one-slack Smirnov mass.  Since that complete mass
is at most three times Ford's natural volume scale, intersecting any family
which already retains one half of the natural scale still leaves one eighth.

All sets and sums in this file are finite.  The final membership theorem
places the retained vectors simultaneously in the size-closed family used
by `SizedBlockBounds` and in the positive family used by
`FixedPositiveBlockMass`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The one-slack, prefix-energy, endpoint-capped family after imposing the
weighted product-size cutoff. -/
noncomputable def fixedLowerSizedRestrictedOccupancies
    (M k : ℕ) (T : ℝ) : Finset (Fin k → ℕ) :=
  (fixedLowerRestrictedOccupancies M k T).filter fun c ↦
    compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k

theorem mem_fixedLowerSizedRestrictedOccupancies
    {M k : ℕ} {T : ℝ} {c : Fin k → ℕ} :
    c ∈ fixedLowerSizedRestrictedOccupancies M k T ↔
      c ∈ smirnovOccupancies k 1 k ∧
      fixedLowerPrefixEnergy c ≤ T ∧ IsFordCapped M c ∧
      compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k := by
  classical
  simp only [fixedLowerSizedRestrictedOccupancies, Finset.mem_filter,
    mem_fixedLowerRestrictedOccupancies]
  tauto

/-- Reciprocal-factorial mass of the size-closed restricted family. -/
noncomputable def fixedLowerSizedRestrictedMass
    (M k : ℕ) (T : ℝ) : ℝ :=
  ∑ c ∈ fixedLowerSizedRestrictedOccupancies M k T,
    1 / compositionFactorial c

/-- The complete one-slack mass is at most three times the natural volume
scale.  This is the elementary bound `(1 + 1/k)^k ≤ e < 3`. -/
theorem smirnovOccupancyMass_one_le_three_scale
    {k : ℕ} (hk : 1 ≤ k) :
    smirnovOccupancyMass k 1 k ≤
      3 * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  rw [smirnovOccupancyMass_one_eq hk, Nat.factorial_succ]
  push_cast
  have hkR : (0 : ℝ) < k := by positivity
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hpow :
      (((k : ℝ) + 1) / (k : ℝ)) ^ k ≤ Real.exp 1 := by
    have h := Real.one_add_inv_pow_le_exp (n := k)
    convert h using 1 <;> field_simp [hkR.ne']
  have hpowThree :
      ((k : ℝ) + 1) ^ k ≤ 3 * (k : ℝ) ^ k := by
    have hkpow : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkR _
    have hratio :
        ((k : ℝ) + 1) ^ k / (k : ℝ) ^ k ≤ Real.exp 1 := by
      simpa [div_pow] using hpow
    have hexp : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
    exact (div_le_iff₀ hkpow).mp (hratio.trans hexp)
  have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpowSucc : ((k : ℝ) + 1) ^ k =
      ((k : ℝ) + 1) ^ (k - 1) * ((k : ℝ) + 1) := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    ((k : ℝ) + 1) ^ (k - 1) / (k.factorial : ℝ) =
        ((k : ℝ) + 1) ^ k /
          (((k : ℝ) + 1) * (k.factorial : ℝ)) := by
      field_simp [hk1R.ne', hfac.ne']
      rw [hpowSucc]
      ring
    _ ≤ (3 * (k : ℝ) ^ k) /
          (((k : ℝ) + 1) * (k.factorial : ℝ)) := by
      exact div_le_div_of_nonneg_right hpowThree
        (mul_nonneg hk1R.le hfac.le)
    _ = 3 * ((k : ℝ) ^ k /
          (((k : ℝ) + 1) * (k.factorial : ℝ))) := by ring

/-- Intersecting a restricted family of mass at least one half of the
natural scale with the size cutoff leaves at least one eighth of that scale.
-/
theorem fixedLowerSizedRestrictedMass_ge_eighth_of_half
    {M k : ℕ} {T : ℝ} (hk : 2 ≤ k)
    (hhalf : (1 / 2 : ℝ) *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
      fixedLowerRestrictedMass M k T) :
    (1 / 8 : ℝ) *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
      fixedLowerSizedRestrictedMass M k T := by
  let R := fixedLowerRestrictedOccupancies M k T
  let G := fixedLowerSizedRestrictedOccupancies M k T
  let B := R.filter fun c ↦
    16 * (2 : ℝ) ^ k < compositionSizeCost c
  let W : (Fin k → ℕ) → ℝ := fun c ↦ 1 / compositionFactorial c
  let L : ℝ := (k : ℝ) ^ k / ((k + 1).factorial : ℝ)
  have hpartition :
      (∑ c ∈ R, W c) = (∑ c ∈ G, W c) + ∑ c ∈ B, W c := by
    rw [show G = R.filter
        (fun c ↦ compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k) by rfl,
      show B = R.filter
        (fun c ↦ 16 * (2 : ℝ) ^ k < compositionSizeCost c) by rfl,
      ← Finset.sum_filter_add_sum_filter_not R
        (fun c ↦ compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k) W]
    congr 2
    ext c
    simp only [Finset.mem_filter, not_le]
  have hBsubset : B ⊆ (smirnovOccupancies k 1 k).filter
      (fun c ↦ 16 * (2 : ℝ) ^ k < compositionSizeCost c) := by
    intro c hc
    have hcData := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨
      (mem_fixedLowerRestrictedOccupancies.mp hcData.1).1, hcData.2⟩
  have hbad : (∑ c ∈ B, W c) ≤ (3 / 8 : ℝ) * L := by
    calc
      (∑ c ∈ B, W c) ≤
          ∑ c ∈ (smirnovOccupancies k 1 k).filter
            (fun c ↦ 16 * (2 : ℝ) ^ k < compositionSizeCost c),
              1 / compositionFactorial c := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hBsubset
        intro c hc hnot
        exact inv_compositionFactorial_nonneg' c
      _ ≤ smirnovOccupancyMass k 1 k / 8 :=
        fixedLowerSizeFailureMass_le_eighth hk
      _ = (1 / 8 : ℝ) * smirnovOccupancyMass k 1 k := by ring
      _ ≤ (1 / 8 : ℝ) * (3 * L) := by
        have hSm := smirnovOccupancyMass_one_le_three_scale
          (k := k) (by omega : 1 ≤ k)
        exact mul_le_mul_of_nonneg_left
          (by simpa [L] using hSm) (by norm_num)
      _ = (3 / 8 : ℝ) * L := by norm_num; ring
  have hR : (1 / 2 : ℝ) * L ≤ ∑ c ∈ R, W c := by
    simpa [R, W, L, fixedLowerRestrictedMass] using hhalf
  rw [hpartition] at hR
  have hG : (1 / 8 : ℝ) * L ≤ ∑ c ∈ G, W c := by
    linarith
  simpa [G, W, L, fixedLowerSizedRestrictedMass] using hG

/-- Closed Markov corollary: the prefix-energy first moment and the size
first moment can be truncated simultaneously, retaining a fixed positive
reciprocal-factorial mass. -/
theorem fixedLowerSizedRestrictedMass_eighth_scale_of_moments
    {M k : ℕ} (hM : 1 ≤ M) (hk : 2 ≤ k) {C : ℝ} (hC : 0 < C)
    (hmoment : fixedLowerPrefixEnergyMoment k ≤
      C * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ))) :
    (1 / 8 : ℝ) *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
      fixedLowerSizedRestrictedMass M k (2 * C) := by
  apply fixedLowerSizedRestrictedMass_ge_eighth_of_half hk
  exact fixedLowerRestrictedMass_half_scale_of_moment hM (by omega) hC hmoment

/-- Every retained vector belongs to the exact size-closed capped family. -/
theorem fixedLowerSizedRestrictedOccupancies_subset_sizedCapped
    {M k : ℕ} (hM : 1 ≤ M) (T : ℝ) :
    fixedLowerSizedRestrictedOccupancies M k T ⊆
      sizedCappedCompositions M k := by
  intro c hc
  have hcData := mem_fixedLowerSizedRestrictedOccupancies.mp hc
  rw [mem_sizedCappedCompositions]
  constructor
  · rw [mem_cappedCompositions]
    exact ⟨(mem_smirnovOccupancies_iff_barrier.mp hcData.1).1,
      smirnovOccupancy_one_isFordCapped hM hcData.1⟩
  · exact hcData.2.2.2

/-- Under Ford's numerical close-pair inequality, every retained vector is
also admitted by the positive block-mass family (with the strict `13/10`
constant used there). -/
theorem fixedLowerSizedRestrictedOccupancies_subset_fordPositive
    {M k : ℕ} {T E Q : ℝ} (hQ : 0 ≤ Q)
    (hquality : Real.exp E * (1 + Q * T) ≤ 13 / 10)
    (hQdef : Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) :
    fixedLowerSizedRestrictedOccupancies M k T ⊆
      fordPositiveCompositions M k E := by
  intro c hc
  have hcData := mem_fixedLowerSizedRestrictedOccupancies.mp hc
  rw [mem_fordPositiveCompositions]
  constructor
  · rw [mem_cappedCompositions]
    exact ⟨(mem_smirnovOccupancies_iff_barrier.mp hcData.1).1,
      hcData.2.2.1⟩
  · rw [← hQdef]
    apply hquality.trans'
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg E)
    simpa [fixedLowerPrefixEnergy] using
      add_le_add_left (mul_le_mul_of_nonneg_left hcData.2.1 hQ) 1

/-- The retained reciprocal-factorial mass is a lower bound for the mass of
Ford-positive vectors which also satisfy the construction-size cutoff. -/
theorem fordPositive_sized_mass_lower_of_fixedLower
    {M k : ℕ} {T E Q B : ℝ} (hM : 1 ≤ M) (hQ : 0 ≤ Q)
    (hquality : Real.exp E * (1 + Q * T) ≤ 13 / 10)
    (hQdef : Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M))
    (hB : B ≤ fixedLowerSizedRestrictedMass M k T) :
    B ≤ ∑ c ∈ (fordPositiveCompositions M k E).filter
        (fun c ↦ c ∈ sizedCappedCompositions M k),
      1 / compositionFactorial c := by
  apply hB.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro c hc
    exact Finset.mem_filter.mpr ⟨
      fixedLowerSizedRestrictedOccupancies_subset_fordPositive
        hQ hquality hQdef hc,
      fixedLowerSizedRestrictedOccupancies_subset_sizedCapped hM T hc⟩
  · intro c hc hnot
    exact inv_compositionFactorial_nonneg' c

/-- Concrete endpoint control for every prime-block integer generated by a
retained vector. -/
theorem fixedLowerSized_blockFamily_le_constructionBound
    {M k : ℕ} (hM : 1 ≤ M) {T : ℝ} {c : Fin k → ℕ}
    (hc : c ∈ fixedLowerSizedRestrictedOccupancies M k T)
    {a : ℕ} (ha : a ∈ compositionBlockFamily M c) :
    a ≤ fordConstructionBound M k := by
  exact sizedBlockFamily_le_constructionBound
    (fixedLowerSizedRestrictedOccupancies_subset_sizedCapped hM T hc) ha

end Erdos446
