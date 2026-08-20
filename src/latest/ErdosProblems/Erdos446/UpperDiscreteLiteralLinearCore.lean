/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDiscreteSourceCover
import ErdosProblems.Erdos446.UpperDiscreteTCoverPublishedCutoff

/-!
# Erdős Problem 446: the literal linear crowding witness

This file is the integration point between the weighted finite `T`-set and
the source-compatible exceptional cover.  Ford's published cutoff is linear
in the cell coordinate (`2*m`) and exponential only in the rank gap (`2^m`).

The hard finite geometric contradiction is proved in
`UpperDiscreteTCoverPublishedCutoff`.  Here we apply it at a deepest affine
prefix and translate its conclusion to `FordLinearCrowdingEvent`, the event
consumed by the source crowding-mass argument.
-/

namespace Erdos446

open Finset

/-- A deepest singular prefix in the weighted finite `T`-set has Ford's
literal crowding witness.  The maximality of `q` is retained in the
hypotheses because it supplies the ambient Smirnov barrier downstream; for
the existence of the crowding scale itself, only its consequence `q ≤ v`
is needed.

In particular, the cell displacement is exactly `2*m`, while the missing
terminal rank block has size `2^m`.
-/
theorem exists_fordLinearCrowdingEvent_of_deepest_weighted
    {v : ℕ} {c : Fin v → ℕ} {q γ r l H : ℕ}
    (hq : IsFordDeepestPrefix γ c q)
    (hl : l = blockPrefixCount c q)
    (hH : H = fordPrefixDepth γ c q)
    (hr : 5 ≤ r) (hdepth : r + 1 ≤ H)
    (hweighted : SatisfiesFordWeightedBarrier γ c) :
    ∃ m, H - 3 ≤ m ∧ FordLinearCrowdingEvent γ m l c := by
  have hsingular :
      2 ^ blockPrefixCount c q ≤
        2 ^ γ * (blockPrefixWeight c q + 1) :=
    hweighted q (Finset.mem_range.mpr (Nat.lt_succ_of_le hq.1))
  have hdepth' :
      r + 1 ≤ blockPrefixCount c q - γ - q + 1 := by
    rw [← fordPrefixDepth]
    simpa only [← hH] using hdepth
  obtain ⟨m, hm, hcrowd⟩ :=
    exists_fordPublishedDyadicCrowdingEvent_of_weighted_singularity
      c q γ r hq.1 hr hdepth' hsingular
  refine ⟨m, ?_, ?_⟩
  · simpa only [hH, fordPrefixDepth] using hm
  · simpa [FordLinearCrowdingEvent, FordPublishedDyadicCrowdingEvent,
      hl] using hcrowd

/-- Expanded form of `exists_fordLinearCrowdingEvent_of_deepest_weighted`,
displaying the two inequalities of Ford's published condition (32j). -/
theorem exists_literal_linear_crowding_of_deepest_weighted
    {v : ℕ} {c : Fin v → ℕ} {q γ r l H : ℕ}
    (hq : IsFordDeepestPrefix γ c q)
    (hl : l = blockPrefixCount c q)
    (hH : H = fordPrefixDepth γ c q)
    (hr : 5 ≤ r) (hdepth : r + 1 ≤ H)
    (hweighted : SatisfiesFordWeightedBarrier γ c) :
    ∃ m, H - 3 ≤ m ∧ 2 ^ m < l ∧
      blockPrefixCount c (l - γ - 2 * m) < l - 2 ^ m := by
  simpa only [FordLinearCrowdingEvent] using
    exists_fordLinearCrowdingEvent_of_deepest_weighted
      hq hl hH hr hdepth hweighted

/-- The literal witness, immediately packaged in the tuple consumed by the
four-factor crowding-mass estimate. -/
theorem exists_fordSourceExceptionalWitness_of_deepest_weighted
    {v : ℕ} {c : Fin v → ℕ} {q γ r l H : ℕ}
    (hq : IsFordDeepestPrefix γ c q)
    (hl : l = blockPrefixCount c q)
    (hH : H = fordPrefixDepth γ c q)
    (hr : 5 ≤ r) (hdepth : r + 1 ≤ H)
    (hweighted : SatisfiesFordWeightedBarrier γ c) :
    ∃ m, FordSourceExceptionalWitness γ r c q H m l := by
  obtain ⟨m, hm, hcrowd⟩ :=
    exists_fordLinearCrowdingEvent_of_deepest_weighted
      hq hl hH hr hdepth hweighted
  refine ⟨m, ?_⟩
  have hdepth' : r + 1 ≤ fordPrefixDepth γ c q := by
    simpa only [← hH] using hdepth
  have hm' : fordPrefixDepth γ c q - 3 ≤ m := by
    simpa only [← hH] using hm
  have hcrowd' :
      FordLinearCrowdingEvent γ m (blockPrefixCount c q) c := by
    simpa only [← hl] using hcrowd
  simpa only [hH, hl] using
    fordSourceExceptionalWitness_of_linear hq hdepth' hm' hcrowd'

/-! ## The closed discrete cover -/

/-- Exact published form of the closed alternative: either the affine
barrier holds, or there are `q,h,m,l` satisfying Ford's literal condition
with cell cutoff `l-γ-2*m` and rank gap `2^m`. -/
theorem fordWeightedOccupancy_affine_or_published_exceptional
    {k v γ : ℕ} {c : Fin v → ℕ}
    (hc : c ∈ fordWeightedOccupancies k v γ) :
    SatisfiesFordAffineBarrier γ (fordDiscreteCoverRadius k v γ) c ∨
      ∃ q h m l,
        FordExceptionalWitness γ
          (fordDiscreteCoverRadius k v γ) c q h m l := by
  have hcData := mem_fordWeightedOccupancies.mp hc
  by_cases haff :
      SatisfiesFordAffineBarrier γ (fordDiscreteCoverRadius k v γ) c
  · exact Or.inl haff
  · right
    obtain ⟨q, hq⟩ := exists_fordDeepestPrefix γ c
    have hdepth :
        fordDiscreteCoverRadius k v γ + 1 ≤ fordPrefixDepth γ c q :=
      deepestPrefix_depth_of_not_affine hq haff
    obtain ⟨m, hm, hcrowd⟩ :=
      exists_fordLinearCrowdingEvent_of_deepest_weighted
        (q := q) (l := blockPrefixCount c q)
        (H := fordPrefixDepth γ c q) hq rfl rfl
        (five_le_fordDiscreteCoverRadius k v γ) hdepth hcData.2
    refine ⟨q, fordPrefixDepth γ c q, m, blockPrefixCount c q, ?_⟩
    rw [FordExceptionalWitness]
    refine ⟨hq.1, rfl, rfl, hdepth, hm, ?_⟩
    simpa only [FordLinearCrowdingEvent, FordDyadicCrowdingEvent] using hcrowd

/-- Every occupancy in the finite weighted `T(k,v,γ)`-set satisfies either
Ford's single affine barrier (32i), at the canonical radius
`max 5 (k-v-γ)`, or has a complete source-compatible exceptional witness
of type (32j).

The witness records a deepest singular prefix.  Its crowding cutoff is the
literal published linear displacement `l-γ-2*m`; the packaged source event
then weakens this to `l-γ-h-2*m`, exactly the cutoff consumed by the
four-factor mass estimate with `u=γ+h` and `s=2*m`. -/
theorem fordWeightedOccupancy_affine_or_exceptional
    {k v γ : ℕ} {c : Fin v → ℕ}
    (hc : c ∈ fordWeightedOccupancies k v γ) :
    SatisfiesFordAffineBarrier γ (fordDiscreteCoverRadius k v γ) c ∨
      ∃ q h m l,
        FordSourceExceptionalWitness γ
          (fordDiscreteCoverRadius k v γ) c q h m l := by
  have hcData := mem_fordWeightedOccupancies.mp hc
  by_cases haff :
      SatisfiesFordAffineBarrier γ (fordDiscreteCoverRadius k v γ) c
  · exact Or.inl haff
  · right
    obtain ⟨q, hq⟩ := exists_fordDeepestPrefix γ c
    have hdepth :
        fordDiscreteCoverRadius k v γ + 1 ≤ fordPrefixDepth γ c q :=
      deepestPrefix_depth_of_not_affine hq haff
    obtain ⟨m, hm⟩ :=
      exists_fordSourceExceptionalWitness_of_deepest_weighted
        (q := q) (l := blockPrefixCount c q)
        (H := fordPrefixDepth γ c q) hq rfl rfl
        (five_le_fordDiscreteCoverRadius k v γ) hdepth hcData.2
    exact ⟨q, fordPrefixDepth γ c q, m, blockPrefixCount c q, hm⟩

/-- Set-theoretic form of `fordWeightedOccupancy_affine_or_exceptional`.
This is the finite exceptional cover used when summing masses. -/
theorem fordWeightedOccupancies_subset_affine_or_exceptional
    (k v γ : ℕ) :
    (fordWeightedOccupancies k v γ : Set (Fin v → ℕ)) ⊆
      {c | SatisfiesFordAffineBarrier γ
        (fordDiscreteCoverRadius k v γ) c} ∪
      {c | ∃ q h m l,
        FordSourceExceptionalWitness γ
          (fordDiscreteCoverRadius k v γ) c q h m l} := by
  intro c hc
  exact fordWeightedOccupancy_affine_or_exceptional hc

/-- Set-cover form retaining Ford's literal published cutoff. -/
theorem fordWeightedOccupancies_subset_affine_or_published_exceptional
    (k v γ : ℕ) :
    (fordWeightedOccupancies k v γ : Set (Fin v → ℕ)) ⊆
      {c | SatisfiesFordAffineBarrier γ
        (fordDiscreteCoverRadius k v γ) c} ∪
      {c | ∃ q h m l,
        FordExceptionalWitness γ
          (fordDiscreteCoverRadius k v γ) c q h m l} := by
  intro c hc
  exact fordWeightedOccupancy_affine_or_published_exceptional hc

end Erdos446
