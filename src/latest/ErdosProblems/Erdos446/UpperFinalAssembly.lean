/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDepthClusterBridge

/-!
# Erdős Problem 446: terminal assembly for the sharp upper bound

This file contains only the final asymptotic assembly.  The finite sieve and
prime-block arguments naturally produce existential constants for
`DyadicUpperSieveClusterReduction` and
`SmoothSquarefreeClusterUpperBlockCount`; the results below remove those
constants and expose the half-open upper bound used by the public theorem.
-/

namespace Erdos446

open Filter Asymptotics
open scoped Topology

/-- The two finite upper estimates imply the half-open Big-O estimate in the
exact normalization used by the final resolution. -/
theorem epsilon_isBigO_growth446_of_sieveCluster_upperBlockCount
    {M : ℕ} {A D : ℝ} {YSieve YCluster : ℕ}
    (hA : 0 < A) (hD : 0 < D)
    (hSieve : DyadicUpperSieveClusterReduction A YSieve)
    (hCluster : SmoothSquarefreeClusterUpperBlockCount M D YCluster) :
    (fun y : ℕ ↦ epsilon y (2 * y)) =O[atTop] growth446 := by
  obtain ⟨D', Y', hD', hCluster'⟩ :=
    exists_smoothSquarefreeClusterModelUpper_of_upperBlockCount hD hCluster
  obtain ⟨C, Y, hC, hY, hPrefix⟩ :=
    exists_dyadicPrefixUpperBound_of_sieveCluster
      hA hD' hSieve hCluster'
  exact epsilon_isBigO_growth446_of_dyadicPrefixUpperBound hY hPrefix

/-- Existential versions of Ford's finite sieve and prime-block estimates are
enough to produce the unconditional half-open upper estimate. -/
theorem epsilon_isBigO_growth446_of_exists_sieveCluster
    (hSieve : ∃ A : ℝ, ∃ Y : ℕ,
      0 < A ∧ DyadicUpperSieveClusterReduction A Y)
    (hCluster : ∃ M : ℕ, ∃ D : ℝ, ∃ Y : ℕ,
      0 < D ∧ SmoothSquarefreeClusterUpperBlockCount M D Y) :
    (fun y : ℕ ↦ epsilon y (2 * y)) =O[atTop] growth446 := by
  obtain ⟨A, YSieve, hA, hSieve⟩ := hSieve
  obtain ⟨M, D, YCluster, hD, hCluster⟩ := hCluster
  exact epsilon_isBigO_growth446_of_sieveCluster_upperBlockCount
    hA hD hSieve hCluster

end Erdos446
