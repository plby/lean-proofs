/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperBlockEnvelope

/-!
# Erdős Problem 446: from the sharp block envelope to arithmetic mass

This short bridge substitutes the pointwise prefix minimum from
`UpperBlockEnvelope` into the reciprocal block-family estimates of
`UpperBlockOccupancy`.  It is the exact one-vector step used before the
Smirnov layer decomposition.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem blockClusterPrefixEnvelope_nonneg
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) (h : ℕ) :
    0 ≤ blockClusterPrefixEnvelope M k b h := by
  dsimp [blockClusterPrefixEnvelope]
  positivity

theorem blockClusterEnvelope_nonneg
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) :
    0 ≤ blockClusterEnvelope M k b := by
  rw [blockClusterEnvelope]
  apply Finset.le_min'
  intro x hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
  exact blockClusterPrefixEnvelope_nonneg M k b h

theorem blockClusterSharpPrefixEnvelope_nonneg
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) (h : ℕ) :
    0 ≤ blockClusterSharpPrefixEnvelope M k b h := by
  dsimp [blockClusterSharpPrefixEnvelope]
  positivity

theorem blockClusterSharpEnvelope_nonneg
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) :
    0 ≤ blockClusterSharpEnvelope M k b := by
  rw [blockClusterSharpEnvelope]
  apply Finset.le_min'
  intro x hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
  exact blockClusterSharpPrefixEnvelope_nonneg M k b h

/-- Exact product-mass estimate with the best sharp prefix envelope inserted.
This is the discrete counterpart of inserting the minimum in Ford's
order-statistics integral. -/
theorem compositionBlockClusterMass_le_sharpEnvelope_product
    {M k v : ℕ} {b : Fin v → ℕ}
    (hb : ∑ i : Fin v, b i = k) :
    compositionBlockClusterMass M b ≤
      blockClusterSharpEnvelope M k b *
        ∏ i : Fin v,
          primeBlockMass (M + i) ^ b i /
            ((b i).factorial : ℝ) := by
  exact compositionBlockClusterMass_le_product
    (blockClusterSharpEnvelope_nonneg M k b)
    (fun a ha ↦ compositionBlock_clusterLength_le_sharpEnvelope hb ha)

/-- Uniform-block-mass version of the preceding exact bridge. -/
theorem compositionBlockClusterMass_le_sharpEnvelope_uniform
    {M k v : ℕ} {b : Fin v → ℕ} {B : ℝ}
    (hb : ∑ i : Fin v, b i = k) (hB : 0 ≤ B)
    (hmass : ∀ i : Fin v, primeBlockMass (M + i) ≤ B) :
    compositionBlockClusterMass M b ≤
      blockClusterSharpEnvelope M k b *
        (B ^ k / compositionFactorial b) := by
  simpa only [hb] using compositionBlockClusterMass_le_uniform hB
    (blockClusterSharpEnvelope_nonneg M k b) hmass
    (fun a ha ↦ compositionBlock_clusterLength_le_sharpEnvelope hb ha)

end Erdos446
