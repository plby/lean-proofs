/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDiscreteTCoverPublishedCutoff

/-!
# Erdős Problem 446: the source-compatible discrete exceptional cover

Ford's published crowding assertion uses a *linear* displacement `2*m` in
the cell coordinate and the exponential rank gap `2^m`.  This is distinct
from the auxiliary power-displacement event proved in
`UpperDiscreteTCoverDyadicCoreAlt`.

This file records the exact source event, chooses a deepest singular prefix,
and proves all structural facts needed to feed the four-factor crowding
estimate: the ambient affine Smirnov barrier, the crossing-prefix equality,
and the weakening from Ford's published cutoff to the `u = γ+h`, `s = 2m`
cutoff.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Integral depth of prefix `q` below the affine line of offset `γ`. -/
def fordPrefixDepth {v : ℕ} (γ : ℕ) (c : Fin v → ℕ) (q : ℕ) : ℕ :=
  blockPrefixCount c q - γ - q + 1

/-- A prefix realizes the largest integral affine depth among all valid
prefixes. -/
def IsFordDeepestPrefix {v : ℕ}
    (γ : ℕ) (c : Fin v → ℕ) (q : ℕ) : Prop :=
  q ≤ v ∧ ∀ t : ℕ, t ≤ v → fordPrefixDepth γ c t ≤ fordPrefixDepth γ c q

theorem exists_fordDeepestPrefix {v : ℕ} (γ : ℕ) (c : Fin v → ℕ) :
    ∃ q, IsFordDeepestPrefix γ c q := by
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image
    (Finset.range (v + 1)) (fordPrefixDepth γ c) (by simp)
  refine ⟨q, ?_⟩
  rw [IsFordDeepestPrefix]
  refine ⟨by
    have := Finset.mem_range.mp hq
    omega, ?_⟩
  intro t ht
  exact hmax t (Finset.mem_range.mpr (by omega))

/-- Ford's literal linear-cutoff crowding event (published (4.7)). -/
def FordLinearCrowdingEvent {v : ℕ}
    (γ m l : ℕ) (c : Fin v → ℕ) : Prop :=
  2 ^ m < l ∧
    blockPrefixCount c (l - γ - 2 * m) < l - 2 ^ m

/-- The weaker cutoff used directly by the four-factor estimate after
putting `u=γ+h` and `s=2m`. -/
def FordSourceCrowdingEvent {v : ℕ}
    (γ h m l : ℕ) (c : Fin v → ℕ) : Prop :=
  2 ^ m < l ∧
    blockPrefixCount c (l - γ - h - 2 * m) < l - 2 ^ m

theorem fordLinearCrowdingEvent_implies_source
    {v γ h m l : ℕ} {c : Fin v → ℕ}
    (hc : FordLinearCrowdingEvent γ m l c) :
    FordSourceCrowdingEvent γ h m l c := by
  rw [FordLinearCrowdingEvent] at hc
  rw [FordSourceCrowdingEvent]
  refine ⟨hc.1, ?_⟩
  exact (blockPrefixCount_monotone c (by omega)).trans_lt hc.2

/-- Complete source-compatible exceptional tuple.  The maximality field is
what supplies the ambient Smirnov barrier required by the volume estimate. -/
def FordSourceExceptionalWitness {v : ℕ}
    (γ r : ℕ) (c : Fin v → ℕ) (q h m l : ℕ) : Prop :=
  IsFordDeepestPrefix γ c q ∧
    l = blockPrefixCount c q ∧
    h = fordPrefixDepth γ c q ∧
    r + 1 ≤ h ∧
    h - 3 ≤ m ∧
    FordSourceCrowdingEvent γ h m l c

theorem deepestPrefix_satisfies_smirnov
    {v γ r q : ℕ} {c : Fin v → ℕ}
    (hq : IsFordDeepestPrefix γ c q)
    (hr0 : 1 ≤ r)
    (hr : r + 1 ≤ fordPrefixDepth γ c q) :
    SatisfiesSmirnovBarrier (γ + fordPrefixDepth γ c q) c := by
  intro t ht htv
  have hdeep := hq.2 t htv
  have hsingular : γ + q < blockPrefixCount c q := by
    by_contra hn
    have hle : blockPrefixCount c q ≤ γ + q := Nat.le_of_not_gt hn
    have hsub : blockPrefixCount c q - γ ≤ q := by omega
    have hzero : blockPrefixCount c q - γ - q = 0 :=
      Nat.sub_eq_zero_of_le hsub
    rw [fordPrefixDepth, hzero] at hr
    omega
  rw [← blockPrefixCount_eq_occupancyPrefix c htv]
  change blockPrefixCount c t <
    γ + (blockPrefixCount c q - γ - q + 1) + t
  simp only [fordPrefixDepth] at hdeep
  by_cases hsmall : blockPrefixCount c t ≤ γ + t
  · omega
  · have hlarge : γ + t < blockPrefixCount c t := lt_of_not_ge hsmall
    omega

theorem deepestPrefix_crossing_index
    {v γ r q : ℕ} {c : Fin v → ℕ}
    (hr0 : 1 ≤ r)
    (hq0 : 1 ≤ q)
    (hr : r + 1 ≤ fordPrefixDepth γ c q) :
    blockPrefixCount c q - (γ + fordPrefixDepth γ c q) + 1 = q := by
  have hsingular : γ + q < blockPrefixCount c q := by
    by_contra hn
    have hle : blockPrefixCount c q ≤ γ + q := Nat.le_of_not_gt hn
    have hsub : blockPrefixCount c q - γ ≤ q := by omega
    have hzero : blockPrefixCount c q - γ - q = 0 :=
      Nat.sub_eq_zero_of_le hsub
    rw [fordPrefixDepth, hzero] at hr
    omega
  rw [fordPrefixDepth]
  let D := blockPrefixCount c q - γ - q
  have hγ : γ ≤ blockPrefixCount c q := by omega
  have hq : q ≤ blockPrefixCount c q - γ := by omega
  have hCeq : blockPrefixCount c q = γ + D + q := by
    dsimp [D]
    omega
  rw [hCeq]
  dsimp [D]
  omega

/-- A deepest prefix whose affine depth is at least `r+1` packages any
published linear-cutoff witness into the exact tuple used by the mass
estimate. -/
theorem fordSourceExceptionalWitness_of_linear
    {v γ r q m : ℕ} {c : Fin v → ℕ}
    (hq : IsFordDeepestPrefix γ c q)
    (hr : r + 1 ≤ fordPrefixDepth γ c q)
    (hm : fordPrefixDepth γ c q - 3 ≤ m)
    (hcrowd : FordLinearCrowdingEvent γ m
      (blockPrefixCount c q) c) :
    FordSourceExceptionalWitness γ r c q
      (fordPrefixDepth γ c q) m (blockPrefixCount c q) := by
  rw [FordSourceExceptionalWitness]
  exact ⟨hq, rfl, rfl, hr, hm,
    fordLinearCrowdingEvent_implies_source hcrowd⟩

/-- Failure of the affine class forces the deepest prefix to have depth at
least `r+1`. -/
theorem deepestPrefix_depth_of_not_affine
    {v γ r q : ℕ} {c : Fin v → ℕ}
    (hq : IsFordDeepestPrefix γ c q)
    (haff : ¬ SatisfiesFordAffineBarrier γ r c) :
    r + 1 ≤ fordPrefixDepth γ c q := by
  simp only [SatisfiesFordAffineBarrier] at haff
  push Not at haff
  obtain ⟨t, htv, hfail⟩ := haff
  have hmax := hq.2 t htv
  have htdepth : r + 1 ≤ fordPrefixDepth γ c t := by
    have hsubgamma : r + t ≤ blockPrefixCount c t - γ := by omega
    have hsubt : r ≤ blockPrefixCount c t - γ - t := by omega
    rw [fordPrefixDepth]
    omega
  exact htdepth.trans hmax

end Erdos446
