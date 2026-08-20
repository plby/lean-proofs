/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperFiniteLayers

/-!
# Erdős Problem 446: exact summation over integral envelope layers

The positive integral envelope assigns every composition of `k` a unique
layer index in `0, ..., k`.  This file records the resulting exact finite
partition both for arbitrary weights and for the block cluster mass.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Sum a weight over the canonical integral layers. -/
theorem sum_blockIntegerDyadicLayers
    {R : Type*} [AddCommMonoid R] (k v : ℕ)
    (f : (Fin v → ℕ) → R) :
    (∑ m ∈ Finset.range (k + 1),
        ∑ b ∈ blockIntegerDyadicLayer k v m, f b) =
      ∑ b ∈ compositionsOf v k, f b := by
  classical
  calc
    (∑ m ∈ Finset.range (k + 1),
        ∑ b ∈ blockIntegerDyadicLayer k v m, f b) =
        ∑ m ∈ Finset.range (k + 1),
          ∑ b ∈ (compositionsOf v k).filter
            (fun b ↦ blockIntegerLayerIndex k b = m), f b := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmle : m ≤ k := by
        have hmlt := Finset.mem_range.mp hm
        omega
      rw [blockIntegerDyadicLayer_eq_indexFiber k v m hmle]
    _ = ∑ b ∈ compositionsOf v k, f b := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      have hindex : blockIntegerLayerIndex k b < k + 1 := by
        have := blockIntegerLayerIndex_le k b
        omega
      rw [Finset.sum_eq_single (blockIntegerLayerIndex k b)]
      · simp
      · intro m hm hne
        rw [if_neg]
        exact fun heq ↦ hne heq.symm
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr hindex))

/-- The full fixed-cardinality block cluster mass is exactly the sum of its
`k+1` canonical integral layers. -/
theorem sum_blockIntegerDyadicLayer_clusterMass
    (M k v : ℕ) :
    (∑ m ∈ Finset.range (k + 1),
        blockClusterMassOver M (blockIntegerDyadicLayer k v m)) =
      blockClusterMassOver M (compositionsOf v k) := by
  simpa only [blockClusterMassOver] using
    sum_blockIntegerDyadicLayers k v (compositionBlockClusterMass M)

end Erdos446
