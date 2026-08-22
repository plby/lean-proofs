/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAwayStoppedLazyOverflow
import ErdosProblems.Erdos1165.HLOZFilteredPastObservability

/-!
# Stopped observability of source-correct away-lazy failures

The away-lazy predicate is evaluated at the actual creation clock.  On a
fixed pair or triple creation atom, it is therefore determined by the
prefix ending at that atom's stopping time.  These are the exact adapters
used by the filtered high/low transition factors.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZAwayStoppedLazyObservability

open HLOZAwayStoppedLazyOverflow HLOZFilteredPastObservability
open HLOZGapFixedPair HLOZGapPointReturn HLOZPathEvents
open HLOZSourceCorrectFilteredTransitions HLOZSpatialAdapter
open HLOZTilingGapRandomClockScreen LazyDecomposition
open StoppedInsertion TilingLazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := (GapScale × GapScale) × GapScale

/-- Away-lazy overflow at a deterministic time depends only on the path
prefix through that time. -/
theorem tilingAwayLazyOverflowAt_iff_of_pathPrefix_eq
    (t : DominoTiling) (o : Orientation)
    {s s' : WalkPath} {n cap : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) :
    TilingAwayLazyOverflowAt t o n cap s ↔
      TilingAwayLazyOverflowAt t o n cap s' := by
  unfold TilingAwayLazyOverflowAt favoriteTilingDominoSites favoriteSites
    pathPhasedBoundaryLocalTime pathPhasedLazyLocalTime
  rw [hp]

/-- On a fixed creation atom, stopped away-lazy overflow reduces to the
literal predicate at the displayed creation time. -/
theorem mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation
    {t : DominoTiling} {o : Orientation} {s : WalkPath}
    {m rank n cap : ℕ}
    (hcreation : ThresholdCreation s m rank n) :
    s ∈ tilingStoppedAwayLazyOverflowEvent t o m rank cap ↔
      TilingAwayLazyOverflowAt t o n cap s := by
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨q, hqCreation, hqOverflow⟩
    have hqn := thresholdCreation_time_unique hqCreation hcreation
    subst q
    exact hqOverflow
  · intro hs
    exact Set.mem_iUnion.mpr ⟨n, hcreation, hs⟩

/-- Rank-one away-lazy failure is observable at a fixed second creation
clock. -/
theorem pairCreationAtom_inter_rankOneAwayLazyCapFailure_observable
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        rankAwayLazyCapFailureEvent t m (cap m) 1)) := by
  apply pairCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz : z.1 ≤ z.2 := (creation_time_lt (by omega) (by omega)
    (by omega) hs.1 hs.2.1).le
  have hp₁ := pathPrefix_eq_of_pathPrefix_eq_of_le hp hz
  have heven :
      s ∈ tilingStoppedAwayLazyOverflowEvent t .even m 1 (cap m) ↔
        s' ∈ tilingStoppedAwayLazyOverflowEvent t .even m 1 (cap m) :=
    (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs.1).trans
      ((tilingAwayLazyOverflowAt_iff_of_pathPrefix_eq t .even hp₁).trans
        (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs'.1).symm)
  have hshifted :
      s ∈ tilingStoppedAwayLazyOverflowEvent t .shifted m 1 (cap m) ↔
        s' ∈ tilingStoppedAwayLazyOverflowEvent t .shifted m 1 (cap m) :=
    (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs.1).trans
      ((tilingAwayLazyOverflowAt_iff_of_pathPrefix_eq t .shifted hp₁).trans
        (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs'.1).symm)
  simp only [rankAwayLazyCapFailureEvent, Set.mem_union, heven, hshifted]

/-- Rank-one away-lazy failure is observable at a fixed third creation
clock. -/
theorem tripleCreationAtom_inter_rankOneAwayLazyCapFailure_observable
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        rankAwayLazyCapFailureEvent t m (cap m) 1)) := by
  apply tripleCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz₁₂ : z.1.1 < z.1.2 := creation_time_lt (by omega) (by omega)
    (by omega) hs.1 hs.2.1
  have hz₂₃ : z.1.2 < z.2 := creation_time_lt (by omega) (by omega)
    (by omega) hs.2.1 hs.2.2.1
  have hz₁ : z.1.1 ≤ z.2 := (hz₁₂.trans hz₂₃).le
  have hp₁ := pathPrefix_eq_of_pathPrefix_eq_of_le hp hz₁
  have heven :
      s ∈ tilingStoppedAwayLazyOverflowEvent t .even m 1 (cap m) ↔
        s' ∈ tilingStoppedAwayLazyOverflowEvent t .even m 1 (cap m) :=
    (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs.1).trans
      ((tilingAwayLazyOverflowAt_iff_of_pathPrefix_eq t .even hp₁).trans
        (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs'.1).symm)
  have hshifted :
      s ∈ tilingStoppedAwayLazyOverflowEvent t .shifted m 1 (cap m) ↔
        s' ∈ tilingStoppedAwayLazyOverflowEvent t .shifted m 1 (cap m) :=
    (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs.1).trans
      ((tilingAwayLazyOverflowAt_iff_of_pathPrefix_eq t .shifted hp₁).trans
        (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs'.1).symm)
  simp only [rankAwayLazyCapFailureEvent, Set.mem_union, heven, hshifted]

/-- Rank-two away-lazy failure is observable at a fixed third creation
clock. -/
theorem tripleCreationAtom_inter_rankTwoAwayLazyCapFailure_observable
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        rankAwayLazyCapFailureEvent t m (cap m) 2)) := by
  apply tripleCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz₂ : z.1.2 ≤ z.2 := (creation_time_lt (by omega) (by omega)
    (by omega) hs.2.1 hs.2.2.1).le
  have hp₂ := pathPrefix_eq_of_pathPrefix_eq_of_le hp hz₂
  have heven :
      s ∈ tilingStoppedAwayLazyOverflowEvent t .even m 2 (cap m) ↔
        s' ∈ tilingStoppedAwayLazyOverflowEvent t .even m 2 (cap m) :=
    (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs.2.1).trans
      ((tilingAwayLazyOverflowAt_iff_of_pathPrefix_eq t .even hp₂).trans
        (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs'.2.1).symm)
  have hshifted :
      s ∈ tilingStoppedAwayLazyOverflowEvent t .shifted m 2 (cap m) ↔
        s' ∈ tilingStoppedAwayLazyOverflowEvent t .shifted m 2 (cap m) :=
    (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs.2.1).trans
      ((tilingAwayLazyOverflowAt_iff_of_pathPrefix_eq t .shifted hp₂).trans
        (mem_tilingStoppedAwayLazyOverflowEvent_iff_of_creation hs'.2.1).symm)
  simp only [rankAwayLazyCapFailureEvent, Set.mem_union, heven, hshifted]

end

end Erdos1165.HLOZAwayStoppedLazyObservability
