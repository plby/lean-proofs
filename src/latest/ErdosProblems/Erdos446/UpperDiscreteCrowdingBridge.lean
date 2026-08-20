/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDiscreteLiteralLinearCore
import ErdosProblems.Erdos446.UpperCrowdingMass

/-!
# Erdős Problem 446: from the discrete T-cover to the crowding mass

This file is the interface between Ford's exceptional witness and the
fixed-rank crowding finset used by the four-factor mass estimate.  It checks
the two index identities explicitly.  For a witness of depth `h`, the
ambient Smirnov parameter is `u = γ+h`; Ford's literal cutoff
`l-γ-2*m` has already been weakened to the required cutoff
`l-γ-h-2*m = l-u-s`, where `s = 2*m`.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- A source-compatible exceptional witness belongs to the precise
fixed-rank crowding finset used by the four-factor mass bound.

The extra hypothesis `1 ≤ r` is automatic for the canonical cover radius,
which is at least five. -/
theorem fordSourceExceptionalWitness_mem_crowdingOccupanciesAt
    {k v γ r q h m l : ℕ} {c : Fin v → ℕ}
    (hr0 : 1 ≤ r) (hsum : ∑ i, c i = k)
    (hw : FordSourceExceptionalWitness γ r c q h m l) :
    c ∈ fordCrowdingOccupanciesAt k (γ + h) v (2 ^ m) (2 * m) l := by
  rcases hw with ⟨hq, hl, hh, hr, hm, hsource⟩
  rw [mem_fordCrowdingOccupanciesAt]
  have hdepth : r + 1 ≤ fordPrefixDepth γ c q := by
    simpa only [← hh] using hr
  have hsmirnov : c ∈ smirnovOccupancies k (γ + h) v := by
    rw [mem_smirnovOccupancies_iff_barrier]
    refine ⟨?_, ?_⟩
    · rw [mem_compositionsOf]
      exact hsum
    · simpa only [hh] using deepestPrefix_satisfies_smirnov hq hr0 hdepth
  have hq0 : 1 ≤ q := by
    by_contra hn
    have hqz : q = 0 := by omega
    subst q
    have hdepthZero : fordPrefixDepth γ c 0 = 1 := by
      simp [fordPrefixDepth, blockPrefixCount]
    rw [hdepthZero] at hdepth
    omega
  have hcross :
      blockPrefixCount c q -
          (γ + fordPrefixDepth γ c q) + 1 = q :=
    deepestPrefix_crossing_index hr0 hq0 hdepth
  have hcross' : l - (γ + h) + 1 = q := by
    simpa only [hl, hh] using hcross
  have hfirst : l ≤ occupancyPrefix c (l - (γ + h) + 1) := by
    rw [hcross', ← blockPrefixCount_eq_occupancyPrefix c hq.1, ← hl]
  have hcutEq :
      l - (γ + h) - 2 * m = l - γ - h - 2 * m := by
    omega
  have hcutq : l - γ - h - 2 * m ≤ q := by
    rw [← hcutEq]
    exact (Nat.sub_le (l - (γ + h)) (2 * m)).trans (by omega)
  have hcutv : l - γ - h - 2 * m ≤ v := hcutq.trans hq.1
  have hsecond :
      occupancyPrefix c (l - (γ + h) - 2 * m) < l - 2 ^ m := by
    rw [hcutEq, ← blockPrefixCount_eq_occupancyPrefix c hcutv]
    exact hsource.2
  exact ⟨hsmirnov, hfirst, hsecond⟩

/-- Canonical-radius specialization of the bridge. -/
theorem fordCanonicalExceptionalWitness_mem_crowdingOccupanciesAt
    {k v γ q h m l : ℕ} {c : Fin v → ℕ}
    (hsum : ∑ i, c i = k)
    (hw : FordSourceExceptionalWitness γ
      (fordDiscreteCoverRadius k v γ) c q h m l) :
    c ∈ fordCrowdingOccupanciesAt k (γ + h) v (2 ^ m) (2 * m) l := by
  exact fordSourceExceptionalWitness_mem_crowdingOccupanciesAt
    (show 1 ≤ fordDiscreteCoverRadius k v γ by
      exact (by omega : 1 ≤ 5).trans
        (five_le_fordDiscreteCoverRadius k v γ)) hsum hw

end Erdos446
