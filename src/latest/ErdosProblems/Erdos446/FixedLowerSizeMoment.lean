/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedLowerCaps
import ErdosProblems.Erdos446.SizedCompositions

/-!
# Erdős Problem 446: size moment on the one-slack Smirnov family

The forward prefix-energy cutoff used for the close-pair estimate does not
by itself control the final coordinates of a composition.  This module
supplies the missing, independent size deletion.  Decreasing one marked
coordinate maps a one-slack occupancy of total mass `k` into the one-slack
occupancies of total mass `k-1`; the latter mass is evaluated by the exact
`u=1, w=2` Smirnov endpoint formula.  Consequently every coordinate has
weighted mean at most two and the double-exponential block-size cost has
first moment at most `2^(k+1)` times the original mass.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem occupancyPrefix_decrement_le {k : ℕ} (i : Fin k)
    (c : Fin k → ℕ) (t : ℕ) :
    occupancyPrefix (decrementComposition i c) t ≤ occupancyPrefix c t := by
  rw [occupancyPrefix, occupancyPrefix]
  apply Finset.sum_le_sum
  intro q hq
  by_cases hqi : q = i
  · subst q
    simp
  · simp [decrementComposition_of_ne hqi]

theorem decrementComposition_mem_smirnov_pred
    {k : ℕ} (hk : 1 ≤ k) (i : Fin k) {c : Fin k → ℕ}
    (hc : c ∈ smirnovOccupancies k 1 k) (hi : 0 < c i) :
    decrementComposition i c ∈ smirnovOccupancies (k - 1) 1 k := by
  rw [mem_smirnovOccupancies]
  constructor
  · have hsum := sum_decrementComposition i c hi
    rw [(mem_smirnovOccupancies.mp hc).1] at hsum
    omega
  · intro t ht htk
    exact lt_of_le_of_lt (occupancyPrefix_decrement_le i c t)
      ((mem_smirnovOccupancies.mp hc).2 t ht htk)

theorem decrementComposition_injOn_pos {k : ℕ} (i : Fin k) :
    Set.InjOn (decrementComposition i)
      {c : Fin k → ℕ | 0 < c i} := by
  intro c hc d hd hcd
  have := congrArg (incrementComposition i) hcd
  simpa [increment_decrementComposition i c hc,
    increment_decrementComposition i d hd] using this

theorem coordinate_div_compositionFactorial_decrement
    {k : ℕ} (i : Fin k) (c : Fin k → ℕ) (hi : 0 < c i) :
    (c i : ℝ) / compositionFactorial c =
      1 / compositionFactorial (decrementComposition i c) := by
  have hinc := compositionFactorial_increment i
    (decrementComposition i c)
  rw [increment_decrementComposition i c hi] at hinc
  have hcoord : decrementComposition i c i + 1 = c i := by
    simp [decrementComposition, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi.ne')]
  rw [hcoord] at hinc
  rw [hinc]
  have hci : (0 : ℝ) < c i := by exact_mod_cast hi
  have hfac : 0 < compositionFactorial (decrementComposition i c) := by
    dsimp [compositionFactorial]
    positivity
  field_simp

/-- Exact mass of the target family after deleting one marked point. -/
theorem smirnovOccupancyMass_pred_one_eq
    {k : ℕ} (hk : 2 ≤ k) :
    smirnovOccupancyMass (k - 1) 1 k =
      2 * ((k + 1 : ℕ) : ℝ) ^ (k - 2) /
        ((k - 1).factorial : ℝ) := by
  have hkpred : 1 ≤ k - 1 := by omega
  have hprob := smirnovProbability_one_eq
    (k := k - 1) (v := k) (w := 2) hkpred (by norm_num) (by omega)
  rw [smirnovProbability] at hprob
  norm_num at hprob
  have hkR : (0 : ℝ) < k := by positivity
  have hkpow : (0 : ℝ) < (k : ℝ) ^ (k - 1) := pow_pos hkR _
  have hfac : (0 : ℝ) < ((k - 1).factorial : ℝ) := by positivity
  have hprob' :
      smirnovOccupancyMass (k - 1) 1 k * ((k - 1).factorial : ℝ) /
          (k : ℝ) ^ (k - 1) =
        2 * ((k + 1 : ℕ) : ℝ) ^ (k - 2) /
          (k : ℝ) ^ (k - 1) := by
    calc
      smirnovOccupancyMass (k - 1) 1 k * ((k - 1).factorial : ℝ) /
            (k : ℝ) ^ (k - 1) =
          ((k - 1).factorial : ℝ) *
            smirnovOccupancyMass (k - 1) 1 k /
              (k : ℝ) ^ (k - 1) := by ring
      _ = 2 * (2 + ((k - 1 : ℕ) : ℝ)) ^ (k - 1 - 1) /
            (k : ℝ) ^ (k - 1) := hprob
      _ = 2 * ((k + 1 : ℕ) : ℝ) ^ (k - 2) /
            (k : ℝ) ^ (k - 1) := by
        have hbase : 2 + ((k - 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ k)]
          push_cast
          ring
        have hexp : k - 1 - 1 = k - 2 := by omega
        rw [hbase, hexp]
  apply (eq_div_iff hfac.ne').2
  apply (div_left_inj' hkpow.ne').mp
  exact hprob'

/-- Deleting one occurrence in a fixed coordinate bounds that coordinate's
first moment by the complete `u=1,w=2` Smirnov mass. -/
theorem fixedLowerCoordinateMoment_le_predMass
    {k : ℕ} (hk : 1 ≤ k) (i : Fin k) :
    (∑ c ∈ smirnovOccupancies k 1 k,
        (c i : ℝ) / compositionFactorial c) ≤
      smirnovOccupancyMass (k - 1) 1 k := by
  classical
  let S := smirnovOccupancies k 1 k
  let P := S.filter fun c ↦ 0 < c i
  let D : (Fin k → ℕ) → (Fin k → ℕ) := decrementComposition i
  have hPS : P ⊆ S := Finset.filter_subset _ _
  have hsource :
      (∑ c ∈ S, (c i : ℝ) / compositionFactorial c) =
        ∑ c ∈ P, (c i : ℝ) / compositionFactorial c := by
    change (∑ c ∈ S, (c i : ℝ) / compositionFactorial c) =
      ∑ c ∈ S.filter (fun c ↦ 0 < c i),
        (c i : ℝ) / compositionFactorial c
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hci : 0 < c i
    · simp [hci]
    · have hzero : c i = 0 := by omega
      simp [hci, hzero]
  have hinj : Set.InjOn D P := by
    intro c hc d hd
    have hcpos : 0 < c i := by
      exact (Finset.mem_filter.mp (show c ∈ S.filter (fun c ↦ 0 < c i) by
        simpa [P] using hc)).2
    have hdpos : 0 < d i := by
      exact (Finset.mem_filter.mp (show d ∈ S.filter (fun c ↦ 0 < c i) by
        simpa [P] using hd)).2
    exact decrementComposition_injOn_pos i
      hcpos hdpos
  have hsubset : P.image D ⊆ smirnovOccupancies (k - 1) 1 k := by
    intro d hd
    obtain ⟨c, hcP, rfl⟩ := Finset.mem_image.mp hd
    have hcpos : 0 < c i := by
      exact (Finset.mem_filter.mp (show c ∈ S.filter (fun c ↦ 0 < c i) by
        simpa [P] using hcP)).2
    exact decrementComposition_mem_smirnov_pred hk i
      (hPS hcP) hcpos
  rw [hsource]
  calc
    (∑ c ∈ P, (c i : ℝ) / compositionFactorial c) =
        ∑ c ∈ P, 1 / compositionFactorial (D c) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hcpos : 0 < c i := by
        exact (Finset.mem_filter.mp (show c ∈ S.filter (fun c ↦ 0 < c i) by
          simpa [P] using hc)).2
      exact coordinate_div_compositionFactorial_decrement i c
        hcpos
    _ = ∑ d ∈ P.image D, 1 / compositionFactorial d := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ d ∈ smirnovOccupancies (k - 1) 1 k,
          1 / compositionFactorial d := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun d hd _ ↦ inv_compositionFactorial_nonneg' d)
    _ = smirnovOccupancyMass (k - 1) 1 k := rfl

/-- Every coordinate has reciprocal-factorial weighted mean at most twice
the mass of the original one-slack region. -/
theorem fixedLowerCoordinateMoment_le_two_mass
    {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    (∑ c ∈ smirnovOccupancies k 1 k,
        (c i : ℝ) / compositionFactorial c) ≤
      2 * smirnovOccupancyMass k 1 k := by
  have hcoord := fixedLowerCoordinateMoment_le_predMass (by omega) i
  rw [smirnovOccupancyMass_pred_one_eq hk] at hcoord
  rw [smirnovOccupancyMass_one_eq (by omega)]
  refine hcoord.trans ?_
  have hkR : (0 : ℝ) < k := by positivity
  have hk1R : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hfac : (0 : ℝ) < ((k - 1).factorial : ℝ) := by positivity
  have hkfac : k.factorial = k * (k - 1).factorial := by
    calc
      k.factorial = (k - 1 + 1).factorial := by congr 1 <;> omega
      _ = (k - 1 + 1) * (k - 1).factorial := Nat.factorial_succ _
      _ = k * (k - 1).factorial := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  rw [hkfac]
  push_cast
  have hpow : ((k : ℝ) + 1) ^ (k - 1) =
      ((k : ℝ) + 1) ^ (k - 2) * ((k : ℝ) + 1) := by
    rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
  rw [hpow]
  let A : ℝ := ((k : ℝ) + 1) ^ (k - 2)
  have hleft0 : 0 ≤ 2 * A / ((k - 1).factorial : ℝ) := by
    dsimp [A]
    positivity
  have hratio : (1 : ℝ) ≤ ((k : ℝ) + 1) / (k : ℝ) := by
    apply (le_div_iff₀ hkR).2
    linarith
  calc
    2 * A / ((k - 1).factorial : ℝ) ≤
        (2 * A / ((k - 1).factorial : ℝ)) *
          (((k : ℝ) + 1) / (k : ℝ)) :=
      le_mul_of_one_le_right hleft0 hratio
    _ = 2 * (A * ((k : ℝ) + 1) /
          ((k : ℝ) * ((k - 1).factorial : ℝ))) := by
      dsimp [A]
      field_simp [hkR.ne', hfac.ne']

/-- The weighted size cost has first moment at most `2^(k+1)` times the
one-slack Smirnov mass. -/
theorem fixedLowerSizeCostMoment_le
    {k : ℕ} (hk : 2 ≤ k) :
    (∑ c ∈ smirnovOccupancies k 1 k,
        compositionSizeCost c / compositionFactorial c) ≤
      (2 : ℝ) ^ (k + 1) * smirnovOccupancyMass k 1 k := by
  calc
    (∑ c ∈ smirnovOccupancies k 1 k,
        compositionSizeCost c / compositionFactorial c) =
      ∑ c ∈ smirnovOccupancies k 1 k, ∑ i : Fin k,
        (2 : ℝ) ^ i.val *
          ((c i : ℝ) / compositionFactorial c) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [compositionSizeCost, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ =
      ∑ i : Fin k, (2 : ℝ) ^ i.val *
        ∑ c ∈ smirnovOccupancies k 1 k,
          (c i : ℝ) / compositionFactorial c := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin k, (2 : ℝ) ^ i.val *
          (2 * smirnovOccupancyMass k 1 k) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (fixedLowerCoordinateMoment_le_two_mass hk i) (by positivity)
    _ = (2 * smirnovOccupancyMass k 1 k) *
          ∑ i : Fin k, (2 : ℝ) ^ i.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (2 * smirnovOccupancyMass k 1 k) * (2 : ℝ) ^ k := by
      apply mul_le_mul_of_nonneg_left (sum_two_pow_fin_le k)
      exact mul_nonneg (by norm_num) (smirnovOccupancyMass_nonneg k 1 k)
    _ = (2 : ℝ) ^ (k + 1) * smirnovOccupancyMass k 1 k := by
      rw [pow_succ]
      ring

/-! ## The independent size truncation -/

/-- Smirnov occupancies which satisfy both the close-pair energy cutoff and
the double-exponential block-size cutoff. -/
noncomputable def fixedLowerSizedEnergyOccupancies
    (k : ℕ) (T : ℝ) : Finset (Fin k → ℕ) := by
  classical
  exact (fixedLowerEnergyOccupancies k T).filter fun c ↦
    compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k

noncomputable def fixedLowerSizedEnergyMass (k : ℕ) (T : ℝ) : ℝ :=
  ∑ c ∈ fixedLowerSizedEnergyOccupancies k T,
    1 / compositionFactorial c

theorem mem_fixedLowerSizedEnergyOccupancies
    {k : ℕ} {T : ℝ} {c : Fin k → ℕ} :
    c ∈ fixedLowerSizedEnergyOccupancies k T ↔
      c ∈ smirnovOccupancies k 1 k ∧
      fixedLowerPrefixEnergy c ≤ T ∧
      compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k := by
  classical
  simp [fixedLowerSizedEnergyOccupancies,
    mem_fixedLowerEnergyOccupancies, and_assoc]

/-- At most one eighth of the one-slack reciprocal-factorial mass violates
the size cutoff. -/
theorem fixedLowerSizeFailureMass_le_eighth
    {k : ℕ} (hk : 2 ≤ k) :
    (∑ c ∈ (smirnovOccupancies k 1 k).filter
        (fun c ↦ 16 * (2 : ℝ) ^ k < compositionSizeCost c),
      1 / compositionFactorial c) ≤
      smirnovOccupancyMass k 1 k / 8 := by
  classical
  let S := smirnovOccupancies k 1 k
  let B := S.filter
    (fun c ↦ 16 * (2 : ℝ) ^ k < compositionSizeCost c)
  let Q : ℝ := 16 * (2 : ℝ) ^ k
  let W : (Fin k → ℕ) → ℝ := fun c ↦ 1 / compositionFactorial c
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hmarkov : Q * (∑ c ∈ B, W c) ≤
      ∑ c ∈ S, compositionSizeCost c / compositionFactorial c := by
    calc
      Q * (∑ c ∈ B, W c) = ∑ c ∈ B, Q * W c := by
        rw [Finset.mul_sum]
      _ ≤ ∑ c ∈ B,
          compositionSizeCost c / compositionFactorial c := by
        apply Finset.sum_le_sum
        intro c hc
        have hcQ : Q ≤ compositionSizeCost c :=
          (Finset.mem_filter.mp hc).2.le
        simpa [W, div_eq_mul_inv] using mul_le_mul_of_nonneg_right hcQ
          (by
            apply inv_nonneg.mpr
            dsimp [compositionFactorial]
            positivity)
      _ ≤ ∑ c ∈ S,
          compositionSizeCost c / compositionFactorial c := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro c hcS hcB
          exact div_nonneg (compositionSizeCost_nonneg c) (by
            dsimp [compositionFactorial]
            positivity)
  have hmoment := hmarkov.trans (fixedLowerSizeCostMoment_le hk)
  have hbad : (∑ c ∈ B, W c) ≤
      ((2 : ℝ) ^ (k + 1) * smirnovOccupancyMass k 1 k) / Q := by
    exact (le_div_iff₀ hQ).2 (by simpa [mul_comm] using hmoment)
  have hsimp :
      ((2 : ℝ) ^ (k + 1) * smirnovOccupancyMass k 1 k) / Q =
        smirnovOccupancyMass k 1 k / 8 := by
    dsimp [Q]
    have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
    rw [pow_succ]
    field_simp [hpow]
    ring
  simpa [S, B, W, hsimp] using hbad

/-- Imposing the size cutoff after the energy cutoff loses at most one
eighth of the original Smirnov mass. -/
theorem fixedLowerSizedEnergyMass_lower
    {k : ℕ} (hk : 2 ≤ k) {T L A : ℝ} (hT : 0 < T)
    (hmass : L ≤ smirnovOccupancyMass k 1 k)
    (hmoment : fixedLowerPrefixEnergyMoment k ≤ A) :
    L - A / T - smirnovOccupancyMass k 1 k / 8 ≤
      fixedLowerSizedEnergyMass k T := by
  classical
  let E := fixedLowerEnergyOccupancies k T
  let G := fixedLowerSizedEnergyOccupancies k T
  let B := E.filter fun c ↦
    16 * (2 : ℝ) ^ k < compositionSizeCost c
  let W : (Fin k → ℕ) → ℝ := fun c ↦ 1 / compositionFactorial c
  have hpartition : (∑ c ∈ E, W c) =
      (∑ c ∈ G, W c) + ∑ c ∈ B, W c := by
    rw [show G = E.filter (fun c ↦
        compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k) by rfl,
      show B = E.filter (fun c ↦
        16 * (2 : ℝ) ^ k < compositionSizeCost c) by rfl]
    rw [← Finset.sum_filter_add_sum_filter_not E
      (fun c ↦ compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k) W]
    congr 2
    ext c
    simp only [Finset.mem_filter, not_le]
  have hbad : (∑ c ∈ B, W c) ≤
      smirnovOccupancyMass k 1 k / 8 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans
      (fixedLowerSizeFailureMass_le_eighth hk)
    · intro c hc
      have hcData := Finset.mem_filter.mp hc
      apply Finset.mem_filter.mpr
      exact ⟨(mem_fixedLowerEnergyOccupancies.mp hcData.1).1, hcData.2⟩
    · intro c hc hnot
      exact inv_compositionFactorial_nonneg' c
  have henergy := fixedLowerEnergyMass_lower_of_moment hT hmass hmoment
  change L - A / T ≤ ∑ c ∈ E, W c at henergy
  change ∑ c ∈ E, W c = ∑ c ∈ G, W c + ∑ c ∈ B, W c at hpartition
  change L - A / T - smirnovOccupancyMass k 1 k / 8 ≤
    ∑ c ∈ G, W c
  linarith

/-- Every fully restricted occupancy lies simultaneously in the explicit
positive-isolation class and in the size-truncated block class. -/
theorem fixedLowerSizedEnergy_subset_positiveIsolated_and_sized
    {M k : ℕ} {T E Q : ℝ} (hM : 1 ≤ M) (hQ : 0 ≤ Q)
    (hquality : Real.exp E * (1 + Q * T) ≤ 4 / 3)
    (hQdef : Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) :
    fixedLowerSizedEnergyOccupancies k T ⊆
      positiveIsolatedCompositions M k E ∩ sizedCappedCompositions M k := by
  intro c hc
  have hcData := mem_fixedLowerSizedEnergyOccupancies.mp hc
  have hcap : c ∈ cappedCompositions M k := by
    rw [mem_cappedCompositions]
    exact ⟨(mem_smirnovOccupancies_iff_barrier.mp hcData.1).1,
      smirnovOccupancy_one_isFordCapped hM hcData.1⟩
  apply Finset.mem_inter.mpr
  constructor
  · rw [mem_positiveIsolatedCompositions]
    refine ⟨hcap, ?_⟩
    rw [← hQdef]
    apply hquality.trans'
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg E)
    simpa [fixedLowerPrefixEnergy, add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_left hcData.2.1 hQ) 1
  · rw [mem_sizedCappedCompositions]
    exact ⟨hcap, hcData.2.2⟩

end Erdos446
