/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZTilingEndpointSourceRowProp49

/-!
# Origin-safe checker coverage on a rankwise past

The fixed-direction source theorem first covers a literal target transition
inside its physical checker pullback.  This adapter then places that witness
in the rankwise rebased family, provided the complete source previous event
belongs to the rank past.  No atom is conditionally cut.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZCheckerOriginSafeRankPastCover

open HLOZCheckerOriginSafeProp49Family
open HLOZCheckerPrefixedCylinderTransport
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceEndpointTransportTable
open HLOZStoppedCandidatePreviousRebase
open HLOZStoppedHistoryCandidateFuture
open HLOZTilingEndpointSourceRowProp49
open LazyDecomposition ScreeningInstantiation

noncomputable section

/-- Exact target-candidate coverage survives rebasing when the whole literal
checker source past is absorbed by the rankwise previous event. -/
theorem checkerOriginSafeNext_subset_rebasedSomeCandidate
    (d : Tilings.CheckerDirection) (e : Direction)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous next : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hold : checkerPrefixedPreimage e
      (targetOriginSafe m k e ∩
        VariableStoppedTracePartition.thresholdReachStage m k) ⊆ previous)
    (hnext : ∀ s ∈ next,
      ∃ (eta : SourceSupportedIndex (shiftedCheckerTarget d) .even m k)
          (candidate : Point),
        s ∈ historyPiece (shiftedCheckerTarget d) .even m k
          (SourceSupportAt (shiftedCheckerTarget d) .even m)
          (targetOriginSafe m k e ∩
            VariableStoppedTracePartition.thresholdReachStage m k)
          (some eta) ∧
        OriginSafeSourceProp49EligibleHistory e eta ∧
        candidate ∈ eta.1.2 ∧
        s ∈ sourceOriginSafeCandidateNear eta a low e candidate) :
    checkerPrefixedPreimage e next ⊆
      (checkerOriginSafeRebasedFamily d e m k a low previous hprevious hm hk
        hwindow harithmetic hwidth hexternalArithmetic).someCandidate := by
  apply (checkerOriginSafeNext_subset_someCandidate
    (t := shiftedCheckerTarget d) (o := .even) a low e next hm hk hwindow
      harithmetic hwidth hexternalArithmetic hnext).trans
  exact
    StoppedHistoryCandidateFamily.someCandidate_subset_rebaseToPrevious_of_subset
      (checkerOriginSafeFamily
        (t := shiftedCheckerTarget d) (o := .even) a low e hm hk hwindow
          harithmetic hwidth hexternalArithmetic)
      previous hprevious hold

end

end Erdos1165.HLOZCheckerOriginSafeRankPastCover
