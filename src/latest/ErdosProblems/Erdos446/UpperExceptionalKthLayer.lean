/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperExceptionalMassBridge
import ErdosProblems.Erdos446.UpperDiscreteTCover

/-!
# Erdős Problem 446: exceptional mass on one arithmetic layer

Ford's exceptional-cover estimate controls the reciprocal-factorial mass of
the proper set `fordWeightedOccupancies k v m`.  It is essential not to
enlarge this set to the ambient Smirnov family: doing so loses the extra
factor `1 / (k + 1)` which turns `k!` into `(k+1)!`.

The theorems below combine the exact set inclusions from
`UpperDiscreteTCover` with the nonuniform prime-block estimate from
`UpperExceptionalMassBridge`.  Thus any exceptional-cover estimate with a
`(k+1)!` denominator is transferred verbatim to the actual arithmetic
cluster mass, at the cost of only one absolute Mertens-error factor.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- A real sharp-envelope layer inherits any reciprocal-factorial bound for
its ambient discrete Ford `T`-set. -/
theorem sharpBlockDyadicLayer_mass_le_of_fordWeightedMass
    {M k v m : ℕ} {C R : ℝ} (hC : 0 ≤ C)
    (hoffset : m + blockLayerSlack k + 1 ≤ 2 ^ M)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hford : reciprocalFactorialMassOver
      (fordWeightedOccupancies k v m) ≤ R) :
    blockClusterMassOver M (sharpBlockDyadicLayer M k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) * R := by
  let A : ℝ :=
    sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity))
      (by positivity)
  have hbase := blockClusterMassOver_le_reciprocalFactorialMass_of_offset
    hC hA hoffset (sharpBlockDyadicLayer_subset_smirnov M k v m)
    hmass (fun b hb a ha ↦ sharpBlockDyadicLayer_clusterLength_le hb ha)
  have hsetMass : reciprocalFactorialMassOver
      (sharpBlockDyadicLayer M k v m) ≤ R :=
    (reciprocalFactorialMassOver_mono
      (sharpBlockDyadicLayer_subset_fordWeightedOccupancies M k v m)).trans
        hford
  exact hbase.trans (mul_le_mul_of_nonneg_left hsetMass (by
    dsimp [A]
    positivity))

/-- A canonical integral layer inherits any reciprocal-factorial bound for
its ambient discrete Ford `T`-set.  This is the form used in the exact
partition of all occupancy vectors. -/
theorem blockIntegerDyadicLayer_mass_le_of_fordWeightedMass
    {M k v m : ℕ} {C R : ℝ} (hC : 0 ≤ C)
    (hoffset : m + blockLayerSlack k + 1 ≤ 2 ^ M)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hford : reciprocalFactorialMassOver
      (fordWeightedOccupancies k v m) ≤ R) :
    blockClusterMassOver M (blockIntegerDyadicLayer k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) * R := by
  let A : ℝ := sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity)
  have hbase := blockClusterMassOver_le_reciprocalFactorialMass_of_offset
    hC hA hoffset (blockIntegerDyadicLayer_subset_smirnov k v m)
    hmass (fun b hb a ha ↦ blockIntegerDyadicLayer_clusterLength_le hb ha)
  have hsetMass : reciprocalFactorialMassOver
      (blockIntegerDyadicLayer k v m) ≤ R :=
    (reciprocalFactorialMassOver_mono
      (blockIntegerDyadicLayer_subset_fordWeightedOccupancies k v m)).trans
        hford
  exact hbase.trans (mul_le_mul_of_nonneg_left hsetMass (by
    dsimp [A]
    positivity))

/-- Canonical-layer wrapper with one `M`-condition uniform in all indices
`m ≤ k`. -/
theorem blockIntegerDyadicLayer_mass_le_of_fordWeightedMass_uniform
    {M k v m : ℕ} {C R : ℝ} (hC : 0 ≤ C) (hmk : m ≤ k)
    (hM : k + blockLayerSlack k + 1 ≤ 2 ^ M)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hford : reciprocalFactorialMassOver
      (fordWeightedOccupancies k v m) ≤ R) :
    blockClusterMassOver M (blockIntegerDyadicLayer k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) * R := by
  have hoffset : m + blockLayerSlack k + 1 ≤ 2 ^ M := by
    have := Nat.add_le_add_right hmk (blockLayerSlack k + 1)
    omega
  exact blockIntegerDyadicLayer_mass_le_of_fordWeightedMass
    hC hoffset hmass hford

/-- Factorial-preserving specialization.  In particular, no passage
through the full Smirnov mass can replace `(k+1)!` by `k!`. -/
theorem blockIntegerDyadicLayer_mass_le_fordExceptional
    {M k v m : ℕ} {C D Y : ℝ} (hC : 0 ≤ C) (hmk : m ≤ k)
    (hM : k + blockLayerSlack k + 1 ≤ 2 ^ M)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hford : reciprocalFactorialMassOver
      (fordWeightedOccupancies k v m) ≤
        D * Y / ((k + 1).factorial : ℝ)) :
    blockClusterMassOver M (blockIntegerDyadicLayer k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
          (D * Y / ((k + 1).factorial : ℝ)) := by
  exact blockIntegerDyadicLayer_mass_le_of_fordWeightedMass_uniform
    hC hmk hM hmass hford

/-- The canonical-layer bridge with the prime-block Mertens estimate fully
instantiated.  The constants `C,J` are absolute; after `M ≥ J`, the only
remaining input is the purely finite reciprocal-factorial estimate for
Ford's weighted occupancy set. -/
theorem exists_blockIntegerDyadicLayer_mass_le_of_fordWeightedMass :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, ∀ M : ℕ, J ≤ M →
      ∀ k v m : ℕ, m ≤ k →
      k + blockLayerSlack k + 1 ≤ 2 ^ M →
      ∀ R : ℝ,
      reciprocalFactorialMassOver (fordWeightedOccupancies k v m) ≤ R →
      blockClusterMassOver M (blockIntegerDyadicLayer k v m) ≤
        (sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)) *
          Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) * R := by
  obtain ⟨C, hC, J, htail⟩ :=
    exists_primeBlockMass_geometric_error_threshold
  refine ⟨C, hC, J, ?_⟩
  intro M hMJ k v m hmk hM R hford
  apply blockIntegerDyadicLayer_mass_le_of_fordWeightedMass_uniform
    hC.le hmk hM (R := R) (hford := hford)
  intro i
  exact htail (M + i.val) (by omega)

end Erdos446
