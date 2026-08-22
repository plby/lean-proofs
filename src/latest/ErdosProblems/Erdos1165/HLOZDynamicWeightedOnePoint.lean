/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.ExternalWeightedOnePoint
import ErdosProblems.Erdos1165.HLOZDynamicThresholdedScreening

/-!
# Stopped-trace summation of the weighted external one-point estimate

`ExternalWeightedOnePoint.externalBlocks_weighted_oneSite` proves the sharp
weighted estimate after the retained-block chain and its length have been
fixed. This module sums that estimate over a countable stopped trace
partition. The remaining hypotheses are literal path/external-block mass
identities, not a walk-space transition inequality.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZDynamicWeightedOnePoint

open ExternalThickCount ExternalWeightedOnePoint ExternalWalk
open ExternalOnePoint ExternalProposition44 ExternalRenewal
open LazyDecomposition

noncomputable section

/-- Exact disintegration of every stopped visited-site event into retained
external-block pieces. The insertion/stopped-past contribution is the scalar
`pastMass`; the two displayed mass equalities identify the remaining factor
with the literal IID retained-block events. -/
structure StoppedExternalBlocksDisintegration
    {Index : Type*} [Countable Index]
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (q : ℝ≥0∞) where
  piece : Point → Index → Set WalkPath
  measurable_piece : ∀ x z, MeasurableSet (piece x z)
  disjoint_piece : ∀ x, Pairwise fun z w ↦ Disjoint (piece x z) (piece x w)
  union_piece : ∀ x, (⋃ z, piece x z) = memberEvent visited x
  orientation : Point → Index → Orientation
  retainedLength : Point → Index → ℕ
  threshold : Point → Index → ℕ
  externalPoint : Point → Index → Point
  pastMass : Point → Index → ℝ≥0∞
  member_mass : ∀ x z,
    simpleRandomWalk (piece x z) = pastMass x z *
      externalBlocks (orientation x z) {eta |
        externalPoint x z ∈
          (externalPositionList (orientation x z) eta
            (retainedLength x z)).toFinset}
  candidate_mass : ∀ x z,
    simpleRandomWalk (piece x z ∩ large x) = pastMass x z *
      externalBlocks (orientation x z) {eta |
        externalPoint x z ∈
            (externalPositionList (orientation x z) eta
              (retainedLength x z)).toFinset ∧
          threshold x z ≤
            listLocalTime
              (externalPositionList (orientation x z) eta
                (retainedLength x z)) (externalPoint x z)}
  origin_tail : ∀ x z,
    externalBlocks (orientation x z) {eta |
      threshold x z ≤
        externalOriginLocalTime (orientation x z) eta
          (retainedLength x z)} ≤ q

/-- On one stopped trace piece, the checked retained-chain theorem gives the
weighted candidate estimate. -/
theorem piece_inter_large_le
    {Index : Type*} [Countable Index]
    {visited : WalkPath → Finset Point} {large : Point → Set WalkPath}
    {q : ℝ≥0∞}
    (data : StoppedExternalBlocksDisintegration
      (Index := Index) visited large q)
    (x : Point) (z : Index) :
    simpleRandomWalk (data.piece x z ∩ large x) ≤
      q * simpleRandomWalk (data.piece x z) := by
  rw [data.candidate_mass x z, data.member_mass x z]
  have h := externalBlocks_weighted_oneSite (data.orientation x z)
    (data.retainedLength x z) (data.threshold x z) q
    (data.origin_tail x z) (data.externalPoint x z)
  calc
    data.pastMass x z *
        externalBlocks (data.orientation x z) {eta |
          data.externalPoint x z ∈
              (externalPositionList (data.orientation x z) eta
                (data.retainedLength x z)).toFinset ∧
            data.threshold x z ≤
              listLocalTime
                (externalPositionList (data.orientation x z) eta
                  (data.retainedLength x z)) (data.externalPoint x z)} ≤
      data.pastMass x z *
        (q * externalBlocks (data.orientation x z) {eta |
          data.externalPoint x z ∈
            (externalPositionList (data.orientation x z) eta
              (data.retainedLength x z)).toFinset}) := by
      gcongr
    _ = q * (data.pastMass x z *
        externalBlocks (data.orientation x z) {eta |
          data.externalPoint x z ∈
            (externalPositionList (data.orientation x z) eta
              (data.retainedLength x z)).toFinset}) := by
      ac_rfl

/-- Summing the piecewise retained-chain estimates supplies exactly the
weighted one-site premise of the dynamic Proposition 4.8 theorem. -/
theorem weighted_oneSite_of_stoppedExternalBlocksDisintegration
    {Index : Type*} [Countable Index]
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (q : ℝ≥0∞)
    (data : StoppedExternalBlocksDisintegration
      (Index := Index) visited large q) :
    ∀ x, simpleRandomWalk (candidateEvent visited large x) ≤
      q * simpleRandomWalk (memberEvent visited x) := by
  intro x
  calc
    simpleRandomWalk (candidateEvent visited large x) =
        simpleRandomWalk ((⋃ z, data.piece x z) ∩ large x) := by
      rw [data.union_piece x]
      rfl
    _ = simpleRandomWalk (⋃ z, data.piece x z ∩ large x) := by
      rw [iUnion_inter]
    _ ≤ ∑' z, simpleRandomWalk (data.piece x z ∩ large x) :=
      measure_iUnion_le _
    _ ≤ ∑' z, q * simpleRandomWalk (data.piece x z) :=
      ENNReal.tsum_le_tsum fun z ↦ piece_inter_large_le data x z
    _ = q * ∑' z, simpleRandomWalk (data.piece x z) :=
      ENNReal.tsum_mul_left
    _ = q * simpleRandomWalk (memberEvent visited x) := by
      rw [← measure_iUnion (data.disjoint_piece x) (data.measurable_piece x),
        data.union_piece x]

end

end Erdos1165.HLOZDynamicWeightedOnePoint
