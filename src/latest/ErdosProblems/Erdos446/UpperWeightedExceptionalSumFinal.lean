/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperExceptionalCoverUnion
import ErdosProblems.Erdos446.UpperCrowdingLayerSum
import ErdosProblems.Erdos446.UpperExceptionalDoubleTail

/-!
# Erdős Problem 446: the closed exceptional `T`-mass sum

This file reindexes every genuine exceptional witness by
`h = r+1+t`, `m = h-3+s`, where
`r = max 5 (k-v-γ)`.  This is the reindexing which lets the shifted
factorial suppression be summed twice without losing the crucial
`1/(k+1)!` factor.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Whether the rectangularly reindexed exceptional family is a genuine
crowding family to which the four-factor estimate applies. -/
def IsFordExceptionalRectIndex (k v γ t s : ℕ) : Prop :=
  let h := fordDiscreteCoverRadius k v γ + 1 + t
  let m := h - 3 + s
  h ≤ k ∧ m ≤ k ∧ 2 ^ m < k

/-- A rectangular exceptional cell.  Invalid cells are empty, so the two
index ranges can subsequently be enlarged without introducing hypotheses. -/
noncomputable def fordExceptionalRectFamily
    (k v γ t s : ℕ) : Finset (Fin v → ℕ) := by
  classical
  let h := fordDiscreteCoverRadius k v γ + 1 + t
  let m := h - 3 + s
  exact if IsFordExceptionalRectIndex k v γ t s then
    fordCrowdingOccupancies k (γ + h) v (2 ^ m) (2 * m)
  else ∅

/-- The finite rectangular cover of all genuine exceptional witnesses. -/
noncomputable def fordExceptionalRectCover
    (k v γ : ℕ) : Finset (Fin v → ℕ) := by
  classical
  exact (Finset.range (k + 1)).biUnion fun t ↦
    (Finset.range (k + 1)).biUnion fun s ↦
      fordExceptionalRectFamily k v γ t s

private theorem index_le_two_pow (m : ℕ) : m ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ m := one_le_pow₀ (by omega)
      omega

/-- Every non-affine weighted occupancy belongs to the rectangular cover.
The proof retains the lower bound on the failed depth which was not stored
in the coarser triple-index cover. -/
theorem fordExceptionalOccupancies_subset_rectCover
    (k v γ : ℕ) :
    fordExceptionalOccupancies k v γ ⊆
      fordExceptionalRectCover k v γ := by
  classical
  intro c hc
  have hcData := mem_fordExceptionalOccupancies.mp hc
  obtain haff | ⟨q, h, m, l, hw⟩ :=
    fordWeightedOccupancy_affine_or_exceptional hcData.1
  · exact (hcData.2 haff).elim
  have htotal := (mem_fordWeightedOccupancies.mp hcData.1).1
  have hmemAt := fordCanonicalExceptionalWitness_mem_crowdingOccupanciesAt
    htotal hw
  rcases hw with ⟨hq, hl, hh, hr, hm, hsource⟩
  have hq0 : 1 ≤ q := by
    by_contra hn
    have hqz : q = 0 := by omega
    subst q
    have hdepthZero : fordPrefixDepth γ c 0 = 1 := by
      simp [fordPrefixDepth, blockPrefixCount]
    rw [hh, hdepthZero] at hr
    have hr5 := five_le_fordDiscreteCoverRadius k v γ
    omega
  have hlk : l ≤ k := by
    have hmono := blockPrefixCount_monotone c hq.1
    have hfinal : blockPrefixCount c v = k := by
      rw [blockPrefixCount_eq_occupancyPrefix c le_rfl,
        occupancyPrefix_at_length, htotal]
    rw [← hl, hfinal] at hmono
    exact hmono
  have hdepth : fordDiscreteCoverRadius k v γ + 1 ≤
      fordPrefixDepth γ c q := by
    rw [← hh]
    exact hr
  have hcross := deepestPrefix_crossing_index
    (γ := γ) (r := fordDiscreteCoverRadius k v γ) (c := c) (q := q)
    (show 1 ≤ fordDiscreteCoverRadius k v γ by
      exact (by omega : 1 ≤ 5).trans
        (five_le_fordDiscreteCoverRadius k v γ)) hq0 hdepth
  have hcross' : l - (γ + h) + 1 = q := by
    simpa only [hl, hh] using hcross
  have hh6 : 6 ≤ h := by
    have hr5 := five_le_fordDiscreteCoverRadius k v γ
    omega
  have hul : γ + h ≤ l := by
    have hformula : h = l - γ - q + 1 := by
      simpa only [hl, fordPrefixDepth] using hh
    omega
  have hgl : 2 ^ m + 1 ≤ l := by exact hsource.1
  have hhK : h ≤ k := by omega
  have hmK : m ≤ k :=
    (index_le_two_pow m).trans (by omega)
  let r := fordDiscreteCoverRadius k v γ
  let t := h - (r + 1)
  let s := m - (h - 3)
  have htEq : r + 1 + t = h := by
    dsimp [t, r]
    omega
  have hsEq : h - 3 + s = m := by
    dsimp [s]
    omega
  have htK : t < k + 1 := by
    dsimp [t]
    omega
  have hsK : s < k + 1 := by
    dsimp [s]
    omega
  have htEq' : fordDiscreteCoverRadius k v γ + 1 + t = h := by
    simpa only [r] using htEq
  have hsEq' :
      (fordDiscreteCoverRadius k v γ + 1 + t) - 3 + s = m := by
    rw [htEq']
    exact hsEq
  have hvalid : IsFordExceptionalRectIndex k v γ t s := by
    change fordDiscreteCoverRadius k v γ + 1 + t ≤ k ∧
      (fordDiscreteCoverRadius k v γ + 1 + t) - 3 + s ≤ k ∧
        2 ^ ((fordDiscreteCoverRadius k v γ + 1 + t) - 3 + s) < k
    rw [htEq', hsEq]
    exact ⟨hhK, hmK, by omega⟩
  have hlIcc : l ∈ Finset.Icc (max (2 ^ m + 1) (γ + h)) k := by
    rw [Finset.mem_Icc]
    exact ⟨max_le hgl hul, hlk⟩
  have hmem : c ∈ fordCrowdingOccupancies k (γ + h) v
      (2 ^ m) (2 * m) :=
    fordCrowdingOccupanciesAt_subset_fordCrowdingOccupancies hlIcc hmemAt
  rw [fordExceptionalRectCover, Finset.mem_biUnion]
  refine ⟨t, Finset.mem_range.mpr htK, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨s, Finset.mem_range.mpr hsK, ?_⟩
  rw [fordExceptionalRectFamily, if_pos hvalid]
  simp only [htEq']
  simpa only [hsEq] using hmem

/-- The exceptional reciprocal-factorial mass is at most the sum over the
finite rectangular cells. -/
theorem reciprocalFactorialMassOver_fordExceptionalOccupancies_le_rect
    (k v γ : ℕ) :
    reciprocalFactorialMassOver (fordExceptionalOccupancies k v γ) ≤
      ∑ t ∈ Finset.range (k + 1),
        ∑ s ∈ Finset.range (k + 1),
          reciprocalFactorialMassOver
            (fordExceptionalRectFamily k v γ t s) := by
  apply (reciprocalFactorialMassOver_mono
    (fordExceptionalOccupancies_subset_rectCover k v γ)).trans
  rw [fordExceptionalRectCover]
  apply (reciprocalFactorialMassOver_biUnion_le
    (Finset.range (k + 1)) fun t ↦
      (Finset.range (k + 1)).biUnion fun s ↦
        fordExceptionalRectFamily k v γ t s).trans
  apply Finset.sum_le_sum
  intro t ht
  exact reciprocalFactorialMassOver_biUnion_le
    (Finset.range (k + 1)) fun s ↦
      fordExceptionalRectFamily k v γ t s

/-- The absolute constant left by the four-factor crowding estimate before
the two finite exceptional sums are performed. -/
noncomputable def fordCrowdingMassConstant : ℝ :=
  4 * 2400 ^ 2 * Real.exp 27 * fordCrowdingStrongSuppressionConstant

theorem fordCrowdingMassConstant_nonneg :
    0 ≤ fordCrowdingMassConstant := by
  rw [fordCrowdingMassConstant]
  exact mul_nonneg (by positivity)
    (fordCrowdingStrongSuppressionConstant_pos.le)

private theorem fordDepth_strictly_past_total
    (k v γ t : ℕ) :
    k < γ + (fordDiscreteCoverRadius k v γ + 1 + t) + v := by
  have hr : k - v - γ ≤ fordDiscreteCoverRadius k v γ := by
    rw [fordDiscreteCoverRadius]
    exact le_max_right _ _
  omega

/-- Pointwise suppressed mass bound for a rectangular cell.  Invalid cells
are empty; valid cells satisfy every hypothesis of the unconditional
Smirnov/crowding theorem by construction. -/
theorem reciprocalFactorialMassOver_fordExceptionalRectFamily_le
    {k v γ t s : ℕ} (hv : 0 < v) (hkv : k ≤ 10 * v) :
    reciprocalFactorialMassOver
        (fordExceptionalRectFamily k v γ t s) ≤
      fordCrowdingMassConstant *
        ((γ + (fordDiscreteCoverRadius k v γ + 1 + t) + 1 : ℕ) : ℝ) *
        (((γ + (fordDiscreteCoverRadius k v γ + 1 + t) + v - k + 1 : ℕ) : ℝ) ^ 2) /
          (2 : ℝ) ^
            (2 ^ ((fordDiscreteCoverRadius k v γ + 1 + t - 3 + s) + 3)) *
        ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  let h := fordDiscreteCoverRadius k v γ + 1 + t
  let m := h - 3 + s
  let w := γ + h + v - k
  by_cases hvalid : IsFordExceptionalRectIndex k v γ t s
  · have hdata := hvalid
    change h ≤ k ∧ m ≤ k ∧ 2 ^ m < k at hdata
    have hpast : k < γ + h + v := by
      dsimp [h]
      exact fordDepth_strictly_past_total k v γ t
    have hw : 0 < w := by dsimp [w]; omega
    have hrel : (γ + h) + v = k + w := by
      dsimp [w]
      omega
    have hm : 3 ≤ m := by
      have hr5 := five_le_fordDiscreteCoverRadius k v γ
      dsimp [m, h]
      omega
    rw [fordExceptionalRectFamily, if_pos hvalid]
    change reciprocalFactorialMassOver
        (fordCrowdingOccupancies k (γ + h) v (2 ^ m) (2 * m)) ≤ _
    have hmain := reciprocalFactorialMassOver_fordDyadicCrowding_le_suppressed
      hv hw hrel hm hdata.2.2 hkv
    rw [fordCrowdingMassConstant]
    simpa only [h, m, w, Nat.cast_add, Nat.cast_one] using hmain
  · rw [fordExceptionalRectFamily, if_neg hvalid]
    rw [reciprocalFactorialMassOver]
    simp only [Finset.sum_empty]
    have hconst := fordCrowdingMassConstant_nonneg
    positivity

/-- Sum over the dyadic crowding scale at one failed depth.  The shifted
suppression makes this at most twice the first term. -/
theorem fordExceptionalRectFamily_sum_scale_le
    {k v γ t : ℕ} (hv : 0 < v) (hkv : k ≤ 10 * v) :
    (∑ s ∈ Finset.range (k + 1),
        reciprocalFactorialMassOver
          (fordExceptionalRectFamily k v γ t s)) ≤
      (2 * fordCrowdingMassConstant) *
        ((γ + (fordDiscreteCoverRadius k v γ + 1 + t) + 1 : ℕ) : ℝ) *
        (((γ + (fordDiscreteCoverRadius k v γ + 1 + t) + v - k + 1 : ℕ) : ℝ) ^ 2) /
          (2 : ℝ) ^ (2 ^ (fordDiscreteCoverRadius k v γ + 1 + t)) *
        ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  let h := fordDiscreteCoverRadius k v γ + 1 + t
  let A := ((γ + h + 1 : ℕ) : ℝ) *
    (((γ + h + v - k + 1 : ℕ) : ℝ) ^ 2)
  let B := (v : ℝ) ^ k / ((k + 1).factorial : ℝ)
  have hh : 3 ≤ h := by
    have hr5 := five_le_fordDiscreteCoverRadius k v γ
    dsimp [h]
    omega
  have hpoint : ∀ s : ℕ,
      reciprocalFactorialMassOver
          (fordExceptionalRectFamily k v γ t s) ≤
        fordCrowdingMassConstant * A * B *
          (1 / (2 : ℝ) ^ (2 ^ (h + s))) := by
    intro s
    have hs := reciprocalFactorialMassOver_fordExceptionalRectFamily_le
      (k := k) (v := v) (γ := γ) (t := t) (s := s) hv hkv
    have hm : (h - 3 + s) + 3 = h + s := by omega
    rw [show fordDiscreteCoverRadius k v γ + 1 + t = h by rfl, hm] at hs
    dsimp only [A, B]
    calc
      reciprocalFactorialMassOver
          (fordExceptionalRectFamily k v γ t s) ≤
          fordCrowdingMassConstant *
            ((γ + h + 1 : ℕ) : ℝ) *
            (((γ + h + v - k + 1 : ℕ) : ℝ) ^ 2) /
              (2 : ℝ) ^ (2 ^ (h + s)) * B := hs
      _ = fordCrowdingMassConstant *
            (((γ + h + 1 : ℕ) : ℝ) *
              (((γ + h + v - k + 1 : ℕ) : ℝ) ^ 2)) * B *
                (1 / (2 : ℝ) ^ (2 ^ (h + s))) := by ring
  have htail := doubleExponentialTailPartial_le h (k + 1)
  calc
    (∑ s ∈ Finset.range (k + 1),
        reciprocalFactorialMassOver
          (fordExceptionalRectFamily k v γ t s)) ≤
        ∑ s ∈ Finset.range (k + 1),
          fordCrowdingMassConstant * A * B *
            (1 / (2 : ℝ) ^ (2 ^ (h + s))) :=
      Finset.sum_le_sum fun s hs ↦ hpoint s
    _ = (fordCrowdingMassConstant * A * B) *
        (∑ s ∈ Finset.range (k + 1),
          1 / (2 : ℝ) ^ (2 ^ (h + s))) := by rw [Finset.mul_sum]
    _ ≤ (fordCrowdingMassConstant * A * B) *
        (2 / (2 : ℝ) ^ (2 ^ h)) := by
      exact mul_le_mul_of_nonneg_left htail (by
        exact mul_nonneg (mul_nonneg fordCrowdingMassConstant_nonneg
          (by dsimp [A]; positivity)) (by dsimp [B]; positivity))
    _ = (2 * fordCrowdingMassConstant) *
        ((γ + h + 1 : ℕ) : ℝ) *
        (((γ + h + v - k + 1 : ℕ) : ℝ) ^ 2) /
          (2 : ℝ) ^ (2 ^ h) * B := by
      dsimp [A]
      ring

/-- Exceptional `T`-mass above the central depth.  Here the failed-depth
sum begins at `k-v-γ`, hence the double-exponential factor on the right. -/
theorem reciprocalFactorialMassOver_fordExceptionalOccupancies_le_high
    {k v γ : ℕ} (hv : 0 < v) (hkv : k ≤ 10 * v)
    (hhigh : v + γ + 5 ≤ k) :
    reciprocalFactorialMassOver (fordExceptionalOccupancies k v γ) ≤
      (2 * fordCrowdingMassConstant *
        ((v : ℝ) ^ k / ((k + 1).factorial : ℝ))) *
          (1664 * ((k - v : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 ^ (k - v - γ))) := by
  let b := k - v
  let r := k - v - γ
  let B := (v : ℝ) ^ k / ((k + 1).factorial : ℝ)
  have hr : fordDiscreteCoverRadius k v γ = r := by
    rw [fordDiscreteCoverRadius, max_eq_right]
    omega
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hpoint : ∀ t : ℕ,
      (∑ s ∈ Finset.range (k + 1),
          reciprocalFactorialMassOver
            (fordExceptionalRectFamily k v γ t s)) ≤
        (2 * fordCrowdingMassConstant * B) *
          (((b + t + 2 : ℕ) : ℝ) * ((t + 2 : ℕ) : ℝ) ^ 2 /
            (2 : ℝ) ^ (2 ^ (r + 1 + t))) := by
    intro t
    have hs := fordExceptionalRectFamily_sum_scale_le
      (k := k) (v := v) (γ := γ) (t := t) hv hkv
    have hA : γ + (r + 1 + t) + 1 = b + t + 2 := by
      dsimp [r, b]
      omega
    have hW : γ + (r + 1 + t) + v - k + 1 = t + 2 := by
      dsimp [r]
      omega
    rw [hr, hA, hW] at hs
    dsimp only [B]
    calc
      (∑ s ∈ Finset.range (k + 1),
          reciprocalFactorialMassOver
            (fordExceptionalRectFamily k v γ t s)) ≤
          (2 * fordCrowdingMassConstant) * ((b + t + 2 : ℕ) : ℝ) *
            ((t + 2 : ℕ) : ℝ) ^ 2 /
              (2 : ℝ) ^ (2 ^ (r + 1 + t)) * B := hs
      _ = (2 * fordCrowdingMassConstant * B) *
          (((b + t + 2 : ℕ) : ℝ) * ((t + 2 : ℕ) : ℝ) ^ 2 /
            (2 : ℝ) ^ (2 ^ (r + 1 + t))) := by ring
  have htail := fordExceptionalHighDepthTail_le
    (b := b) (r := r) hb (k + 1)
  calc
    reciprocalFactorialMassOver (fordExceptionalOccupancies k v γ) ≤
        ∑ t ∈ Finset.range (k + 1),
          ∑ s ∈ Finset.range (k + 1),
            reciprocalFactorialMassOver
              (fordExceptionalRectFamily k v γ t s) :=
      reciprocalFactorialMassOver_fordExceptionalOccupancies_le_rect k v γ
    _ ≤ ∑ t ∈ Finset.range (k + 1),
        (2 * fordCrowdingMassConstant * B) *
          (((b + t + 2 : ℕ) : ℝ) * ((t + 2 : ℕ) : ℝ) ^ 2 /
            (2 : ℝ) ^ (2 ^ (r + 1 + t))) :=
      Finset.sum_le_sum fun t ht ↦ hpoint t
    _ = (2 * fordCrowdingMassConstant * B) *
        fordExceptionalHighDepthTail b r (k + 1) := by
      rw [fordExceptionalHighDepthTail, Finset.mul_sum]
    _ ≤ (2 * fordCrowdingMassConstant * B) *
        (1664 * (b : ℝ) / (2 : ℝ) ^ (2 ^ r)) := by
      exact mul_le_mul_of_nonneg_left htail (by
        exact mul_nonneg (mul_nonneg (by positivity)
          fordCrowdingMassConstant_nonneg) (by dsimp [B]; positivity))
    _ = (2 * fordCrowdingMassConstant *
        ((v : ℝ) ^ k / ((k + 1).factorial : ℝ))) *
          (1664 * ((k - v : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 ^ (k - v - γ))) := by
      rfl

/-- Exceptional `T`-mass at or below the central depth.  In this range the
cover radius is five and the remaining depth sum is polynomial. -/
theorem reciprocalFactorialMassOver_fordExceptionalOccupancies_le_low
    {k v γ : ℕ} (hv : 0 < v) (hkv : k ≤ 10 * v)
    (hlow : k < v + γ + 5) :
    reciprocalFactorialMassOver (fordExceptionalOccupancies k v γ) ≤
      (2 * fordCrowdingMassConstant *
        ((v : ℝ) ^ k / ((k + 1).factorial : ℝ))) *
          (52416 * ((γ + 1 : ℕ) : ℝ) *
            ((γ + 5 + v - k : ℕ) : ℝ) ^ 2) := by
  let δ := γ + 5 + v - k
  let B := (v : ℝ) ^ k / ((k + 1).factorial : ℝ)
  have hr : fordDiscreteCoverRadius k v γ = 5 := by
    rw [fordDiscreteCoverRadius, max_eq_left]
    omega
  have hδ : 1 ≤ δ := by dsimp [δ]; omega
  have hpoint : ∀ t : ℕ,
      (∑ s ∈ Finset.range (k + 1),
          reciprocalFactorialMassOver
            (fordExceptionalRectFamily k v γ t s)) ≤
        (2 * fordCrowdingMassConstant * B) *
          (((γ + t + 7 : ℕ) : ℝ) * ((δ + t + 2 : ℕ) : ℝ) ^ 2 /
            (2 : ℝ) ^ (2 ^ (6 + t))) := by
    intro t
    have hs := fordExceptionalRectFamily_sum_scale_le
      (k := k) (v := v) (γ := γ) (t := t) hv hkv
    have hA : γ + (5 + 1 + t) + 1 = γ + t + 7 := by omega
    have hW : γ + (5 + 1 + t) + v - k + 1 = δ + t + 2 := by
      dsimp [δ]
      omega
    rw [hr, hA, hW, show 5 + 1 + t = 6 + t by omega] at hs
    dsimp only [B]
    calc
      (∑ s ∈ Finset.range (k + 1),
          reciprocalFactorialMassOver
            (fordExceptionalRectFamily k v γ t s)) ≤
          (2 * fordCrowdingMassConstant) * ((γ + t + 7 : ℕ) : ℝ) *
            ((δ + t + 2 : ℕ) : ℝ) ^ 2 /
              (2 : ℝ) ^ (2 ^ (6 + t)) * B := hs
      _ = (2 * fordCrowdingMassConstant * B) *
          (((γ + t + 7 : ℕ) : ℝ) * ((δ + t + 2 : ℕ) : ℝ) ^ 2 /
            (2 : ℝ) ^ (2 ^ (6 + t))) := by ring
  have htail := fordExceptionalLowDepthTail_le
    (γ := γ) (δ := δ) hδ (k + 1)
  calc
    reciprocalFactorialMassOver (fordExceptionalOccupancies k v γ) ≤
        ∑ t ∈ Finset.range (k + 1),
          ∑ s ∈ Finset.range (k + 1),
            reciprocalFactorialMassOver
              (fordExceptionalRectFamily k v γ t s) :=
      reciprocalFactorialMassOver_fordExceptionalOccupancies_le_rect k v γ
    _ ≤ ∑ t ∈ Finset.range (k + 1),
        (2 * fordCrowdingMassConstant * B) *
          (((γ + t + 7 : ℕ) : ℝ) * ((δ + t + 2 : ℕ) : ℝ) ^ 2 /
            (2 : ℝ) ^ (2 ^ (6 + t))) :=
      Finset.sum_le_sum fun t ht ↦ hpoint t
    _ = (2 * fordCrowdingMassConstant * B) *
        fordExceptionalLowDepthTail γ δ (k + 1) := by
      rw [fordExceptionalLowDepthTail, Finset.mul_sum]
    _ ≤ (2 * fordCrowdingMassConstant * B) *
        (52416 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left htail (by
        exact mul_nonneg (mul_nonneg (by positivity)
          fordCrowdingMassConstant_nonneg) (by dsimp [B]; positivity))
    _ = (2 * fordCrowdingMassConstant *
        ((v : ℝ) ^ k / ((k + 1).factorial : ℝ))) *
          (52416 * ((γ + 1 : ℕ) : ℝ) *
            ((γ + 5 + v - k : ℕ) : ℝ) ^ 2) := by
      rfl

/-- Absolute constant for the high-depth weighted `T` estimate. -/
noncomputable def fordWeightedHighMassConstant : ℝ :=
  3328 * fordCrowdingMassConstant

/-- Absolute constant for the low-depth weighted `T` estimate, including
both the affine and exceptional alternatives. -/
noncomputable def fordWeightedLowMassConstant : ℝ :=
  57600 + 104832 * fordCrowdingMassConstant

theorem fordWeightedHighMassConstant_nonneg :
    0 ≤ fordWeightedHighMassConstant := by
  rw [fordWeightedHighMassConstant]
  exact mul_nonneg (by norm_num) fordCrowdingMassConstant_nonneg

theorem fordWeightedLowMassConstant_nonneg :
    0 ≤ fordWeightedLowMassConstant := by
  rw [fordWeightedLowMassConstant]
  exact add_nonneg (by norm_num)
    (mul_nonneg (by norm_num) fordCrowdingMassConstant_nonneg)

/-- The closed high-depth bound for the whole weighted Ford family.  The
affine alternative is empty in this range. -/
theorem reciprocalFactorialMassOver_fordWeightedOccupancies_le_high
    {k v γ : ℕ} (hv : 0 < v) (hkv : k ≤ 10 * v)
    (hhigh : v + γ + 5 ≤ k) :
    reciprocalFactorialMassOver (fordWeightedOccupancies k v γ) ≤
      fordWeightedHighMassConstant * ((k - v : ℕ) : ℝ) /
        (2 : ℝ) ^ (2 ^ (k - v - γ)) *
          ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  have hsplit := reciprocalFactorialMassOver_fordWeightedOccupancies_le_split
    k v γ
  have haff := fordCanonicalAffineOccupancies_eq_empty_high hv hhigh
  have hex := reciprocalFactorialMassOver_fordExceptionalOccupancies_le_high
    hv hkv hhigh
  rw [haff] at hsplit
  have hempty : reciprocalFactorialMassOver
      (∅ : Finset (Fin v → ℕ)) = 0 := by
    simp [reciprocalFactorialMassOver]
  rw [hempty, zero_add] at hsplit
  apply hsplit.trans
  apply hex.trans_eq
  rw [fordWeightedHighMassConstant]
  ring

/-- The closed low-depth bound for the whole weighted Ford family.  The
affine and exceptional alternatives have the same natural polynomial
weight and the same `v^k/(k+1)!` normalization. -/
theorem reciprocalFactorialMassOver_fordWeightedOccupancies_le_low
    {k v γ : ℕ} (hv : 0 < v) (hkv : k ≤ 10 * v)
    (hlow : k < v + γ + 5) :
    reciprocalFactorialMassOver (fordWeightedOccupancies k v γ) ≤
      fordWeightedLowMassConstant * ((γ + 1 : ℕ) : ℝ) *
        ((γ + 5 + v - k : ℕ) : ℝ) ^ 2 *
          ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  have hsplit := reciprocalFactorialMassOver_fordWeightedOccupancies_le_split
    k v γ
  have haff := fordCanonicalAffineOccupancies_mass_le_low
    (k := k) (v := v) (γ := γ) (by omega)
  have hex := reciprocalFactorialMassOver_fordExceptionalOccupancies_le_low
    hv hkv hlow
  apply hsplit.trans
  apply (add_le_add haff hex).trans_eq
  rw [fordWeightedLowMassConstant]
  ring

end Erdos446
