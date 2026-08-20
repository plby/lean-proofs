/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperExceptionalCoverUnion
import ErdosProblems.Erdos446.UpperExceptionalKthLayer

/-!
# Erdős Problem 446: the closed exceptional cover on one arithmetic layer

This file closes the set-theoretic part of Ford's finite `T`-cover.  The
weighted occupancy family is the union of its affine part and its non-affine
part; the latter is covered by the finite family of valid crowding indices.
The last theorem transfers this fully concrete cover to the actual
nonuniform prime-product cluster mass on one canonical layer.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Exact partition into the canonical affine and non-affine pieces. -/
theorem fordWeightedOccupancies_eq_affine_union_exceptional
    (k v γ : ℕ) :
    fordWeightedOccupancies k v γ =
      fordAffineOccupancies k v γ (fordDiscreteCoverRadius k v γ) ∪
        fordExceptionalOccupancies k v γ := by
  classical
  ext c
  simp only [fordAffineOccupancies, fordExceptionalOccupancies,
    Finset.mem_union, Finset.mem_filter]
  tauto

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

/-- Closed reciprocal-factorial bound for the whole weighted Ford family:
one affine mass plus the explicit finite sum over every valid crowding
triple. -/
theorem reciprocalFactorialMassOver_fordWeightedOccupancies_le_cover
    (k v γ : ℕ) :
    reciprocalFactorialMassOver (fordWeightedOccupancies k v γ) ≤
      reciprocalFactorialMassOver
          (fordAffineOccupancies k v γ (fordDiscreteCoverRadius k v γ)) +
        ∑ z ∈ fordCrowdingIndices k v γ,
          reciprocalFactorialMassOver
            (fordCrowdingOccupanciesAt k (γ + z.1) v
              (2 ^ z.2.1) (2 * z.2.1) z.2.2) := by
  rw [fordWeightedOccupancies_eq_affine_union_exceptional]
  apply (reciprocalFactorialMassOver_union_le _ _).trans
  simpa only [add_comm] using
    add_le_add_left
      (reciprocalFactorialMassOver_fordExceptionalOccupancies_le k v γ)
      (reciprocalFactorialMassOver
        (fordAffineOccupancies k v γ (fordDiscreteCoverRadius k v γ)))

/-- The actual nonuniform prime-product cluster mass on one canonical layer,
with Ford's full finite exceptional cover substituted.  No enlargement to
the ambient Smirnov family occurs. -/
theorem blockIntegerDyadicLayer_mass_le_fordExceptionalCover
    {M k v m : ℕ} {C : ℝ} (hC : 0 ≤ C) (hmk : m ≤ k)
    (hM : k + blockLayerSlack k + 1 ≤ 2 ^ M)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val)) :
    blockClusterMassOver M (blockIntegerDyadicLayer k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
          (reciprocalFactorialMassOver
              (fordAffineOccupancies k v m
                (fordDiscreteCoverRadius k v m)) +
            ∑ z ∈ fordCrowdingIndices k v m,
              reciprocalFactorialMassOver
                (fordCrowdingOccupanciesAt k (m + z.1) v
                  (2 ^ z.2.1) (2 * z.2.1) z.2.2)) := by
  apply blockIntegerDyadicLayer_mass_le_of_fordWeightedMass_uniform
    hC hmk hM hmass
  exact reciprocalFactorialMassOver_fordWeightedOccupancies_le_cover k v m

end Erdos446
