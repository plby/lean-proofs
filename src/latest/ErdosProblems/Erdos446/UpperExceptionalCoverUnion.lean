/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDiscreteCrowdingBridge
import ErdosProblems.Erdos446.UpperFordAffineMass

/-!
# Erdős Problem 446: a finite union for the exceptional T-cover

This module turns the existential source-compatible witness into one finite
union of the precise crowding families used by the four-factor estimate.
The index set records every side condition of that estimate; hence later
summation never has to bound spurious parameter tuples.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The part of Ford's weighted occupancy family not satisfying its
canonical affine alternative. -/
noncomputable def fordExceptionalOccupancies (k v γ : ℕ) :
    Finset (Fin v → ℕ) := by
  classical
  exact (fordWeightedOccupancies k v γ).filter fun c ↦
    ¬ SatisfiesFordAffineBarrier γ
      (fordDiscreteCoverRadius k v γ) c

theorem mem_fordExceptionalOccupancies
    {k v γ : ℕ} {c : Fin v → ℕ} :
    c ∈ fordExceptionalOccupancies k v γ ↔
      c ∈ fordWeightedOccupancies k v γ ∧
        ¬ SatisfiesFordAffineBarrier γ
          (fordDiscreteCoverRadius k v γ) c := by
  simp [fordExceptionalOccupancies]

/-- A triple `(h,m,l)` for which the fixed-rank four-factor estimate is
applicable after `u=γ+h`, `g=2^m`, and `s=2m`. -/
def IsFordCrowdingIndex (k v γ : ℕ) (z : ℕ × ℕ × ℕ) : Prop :=
  let h := z.1
  let m := z.2.1
  let l := z.2.2
  2 ^ m + 1 ≤ l ∧ γ + h ≤ l ∧ l - (γ + h) < v ∧ h - 3 ≤ m

/-- All relevant crowding indices are automatically bounded by `k`. -/
noncomputable def fordCrowdingIndices (k v γ : ℕ) :
    Finset (ℕ × ℕ × ℕ) := by
  classical
  exact ((Finset.range (k + 1)).product
    ((Finset.range (k + 1)).product (Finset.range (k + 1)))).filter
      (IsFordCrowdingIndex k v γ)

theorem mem_fordCrowdingIndices {k v γ h m l : ℕ} :
    (h, m, l) ∈ fordCrowdingIndices k v γ ↔
      h ≤ k ∧ m ≤ k ∧ l ≤ k ∧
      2 ^ m + 1 ≤ l ∧ γ + h ≤ l ∧
        l - (γ + h) < v ∧ h - 3 ≤ m := by
  classical
  simp [fordCrowdingIndices, IsFordCrowdingIndex]
  omega

/-- Finite union of all valid source crowding families. -/
noncomputable def fordCrowdingCover (k v γ : ℕ) :
    Finset (Fin v → ℕ) := by
  classical
  exact (fordCrowdingIndices k v γ).biUnion fun z ↦
    fordCrowdingOccupanciesAt k (γ + z.1) v
      (2 ^ z.2.1) (2 * z.2.1) z.2.2

private theorem index_le_two_pow (m : ℕ) : m ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ m := one_le_pow₀ (by omega)
      omega

/-- Every non-affine member supplied by the closed discrete T-cover belongs
to the finite crowding union. -/
theorem fordExceptionalOccupancies_subset_crowdingCover
    (k v γ : ℕ) :
    fordExceptionalOccupancies k v γ ⊆ fordCrowdingCover k v γ := by
  classical
  intro c hc
  have hcData := mem_fordExceptionalOccupancies.mp hc
  obtain haff | ⟨q, h, m, l, hw⟩ :=
    fordWeightedOccupancy_affine_or_exceptional hcData.1
  · exact (hcData.2 haff).elim
  have htotal := (mem_fordWeightedOccupancies.mp hcData.1).1
  have hmem := fordCanonicalExceptionalWitness_mem_crowdingOccupanciesAt
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
  have hformula : h = l - γ - q + 1 := by
    simpa only [hl, fordPrefixDepth] using hh
  have hul : γ + h ≤ l := by omega
  have hdiff : l - (γ + h) = q - 1 := by omega
  have hhv : l - (γ + h) < v := by
    rw [hdiff]
    have hqv : q ≤ v := hq.1
    omega
  have hhK : h ≤ k := by omega
  have hgl : 2 ^ m + 1 ≤ l := by
    exact hsource.1
  have hmK : m ≤ k := by
    exact (index_le_two_pow m).trans (by omega)
  have hz : (h, m, l) ∈ fordCrowdingIndices k v γ := by
    rw [mem_fordCrowdingIndices]
    exact ⟨hhK, hmK, hlk, hgl, hul, hhv, hm⟩
  rw [fordCrowdingCover, Finset.mem_biUnion]
  exact ⟨(h, m, l), hz, hmem⟩

private theorem reciprocalFactorialMassOver_union_le
    {v : ℕ} (A B : Finset (Fin v → ℕ)) :
    reciprocalFactorialMassOver (A ∪ B) ≤
      reciprocalFactorialMassOver A + reciprocalFactorialMassOver B := by
  rw [reciprocalFactorialMassOver, reciprocalFactorialMassOver,
    reciprocalFactorialMassOver]
  have hid := Finset.sum_union_inter
    (s₁ := A) (s₂ := B) (f := fun c ↦ 1 / compositionFactorial c)
  have hinter : 0 ≤ ∑ c ∈ A ∩ B, 1 / compositionFactorial c := by
    apply Finset.sum_nonneg
    intro c hc
    apply one_div_nonneg.mpr
    dsimp [compositionFactorial]
    positivity
  linarith

/-- The weighted Ford set is the union of its canonical affine and
exceptional alternatives, so its mass is bounded by the sum of their
masses. -/
theorem reciprocalFactorialMassOver_fordWeightedOccupancies_le_split
    (k v γ : ℕ) :
    reciprocalFactorialMassOver (fordWeightedOccupancies k v γ) ≤
      reciprocalFactorialMassOver
          (fordAffineOccupancies k v γ
            (fordDiscreteCoverRadius k v γ)) +
        reciprocalFactorialMassOver
          (fordExceptionalOccupancies k v γ) := by
  classical
  have hsubset : fordWeightedOccupancies k v γ ⊆
      fordAffineOccupancies k v γ
          (fordDiscreteCoverRadius k v γ) ∪
        fordExceptionalOccupancies k v γ := by
    intro c hc
    by_cases haff : SatisfiesFordAffineBarrier γ
        (fordDiscreteCoverRadius k v γ) c
    · exact Finset.mem_union_left _
        (mem_fordAffineOccupancies.mpr ⟨hc, haff⟩)
    · exact Finset.mem_union_right _
        (mem_fordExceptionalOccupancies.mpr ⟨hc, haff⟩)
  exact (reciprocalFactorialMassOver_mono hsubset).trans
    (reciprocalFactorialMassOver_union_le _ _)

private theorem reciprocalFactorialMassOver_biUnion_le
    {v : ℕ} {T : Type*} [DecidableEq T]
    (S : Finset T) (F : T → Finset (Fin v → ℕ)) :
    reciprocalFactorialMassOver (S.biUnion F) ≤
      ∑ z ∈ S, reciprocalFactorialMassOver (F z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [reciprocalFactorialMassOver]
  | @insert z S hz ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hz]
      exact (reciprocalFactorialMassOver_union_le (F z) (S.biUnion F)).trans
        (add_le_add_right ih _)

/-- The mass of the exceptional part is at most the explicit finite sum of
the valid fixed-rank crowding masses. -/
theorem reciprocalFactorialMassOver_fordExceptionalOccupancies_le :
    ∀ k v γ : ℕ,
    reciprocalFactorialMassOver (fordExceptionalOccupancies k v γ) ≤
      ∑ z ∈ fordCrowdingIndices k v γ,
        reciprocalFactorialMassOver
          (fordCrowdingOccupanciesAt k (γ + z.1) v
            (2 ^ z.2.1) (2 * z.2.1) z.2.2) := by
  intro k v γ
  exact (reciprocalFactorialMassOver_mono
    (fordExceptionalOccupancies_subset_crowdingCover k v γ)).trans
      (reciprocalFactorialMassOver_biUnion_le
        (fordCrowdingIndices k v γ) fun z ↦
          fordCrowdingOccupanciesAt k (γ + z.1) v
            (2 ^ z.2.1) (2 * z.2.1) z.2.2)

end Erdos446
