/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZNoLazyCandidateLocalSeries
import ErdosProblems.Erdos1165.HLOZNoLazyFullBetaDirectSeries
import ErdosProblems.Erdos1165.HLOZRawFullGapProductPromotion

/-!
# No-lazy full-gap series assembly seam

This nonfinal adapter composes every carrier-independent step of the source-low
product proof.  It intentionally exposes the three exact source-side series
that the corrected screened carriers must close: the positive-interface
balance remainder, the oriented shell-source remainder, and the named
low-external complement.  There is no Harnack, global lazy, coefficient-tail,
or arbitrary product-event premise.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZNoLazyFullGapSeriesAssembly

open HLOZCandidateLocalLazyCap HLOZNoLazyCandidateLocalSeries
open HLOZNoLazyFullBetaDirectSeries HLOZNoLazyFullBetaProductBranch
open HLOZRawFullGapProductPromotion HLOZSourceCorrectFullGapClosure

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem measure_union_series_ne_top
    {first second : ℕ → Set WalkPath}
    (hfirst : ∑' m, simpleRandomWalk (first m) ≠ ∞)
    (hsecond : ∑' m, simpleRandomWalk (second m) ≠ ∞) :
    ∑' m, simpleRandomWalk (first m ∪ second m) ≠ ∞ := by
  have hmajor : ∑' m,
      (simpleRandomWalk (first m) + simpleRandomWalk (second m)) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hfirst, hsecond⟩
  exact ne_top_of_le_ne_top hmajor
    (ENNReal.tsum_le_tsum fun m ↦ measure_union_le _ _)

/-- Complete carrier-independent assembly from the three literal source-side
series.  The final screened-carrier modules will prove those three inputs and
invoke this theorem internally. -/
theorem simpleRandomWalk_hlozExceptional_series_ne_top_of_balance_source_series
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling)
    (hbalance : ∑' m, simpleRandomWalk
      (candidateLocalProductPositiveInterfaceBalanceRemainderEvent data t m) ≠ ∞)
    (hsource : ∑' m, simpleRandomWalk
      (candidateLocalProductOrientedSourceEvent data t m) ≠ ∞)
    (hcomplement : ∑' m, simpleRandomWalk
      (onTimeProductBetaCandidateLocalComplementEvent t m
        (data.externalThreshold m)) ≠ ∞) :
    ∑' m, simpleRandomWalk (HLOZPathEvents.hlozExceptionalEvent t m) ≠ ∞ := by
  have hoverflowRaw :=
    simpleRandomWalk_candidateLocalProductOverflowEvent_series_ne_top_of_balance_and_source
      hProp13 data t hbalance hsource
  have hoverflow : ∑' m, simpleRandomWalk
      (HLOZNoLazyCandidateRankSplit.candidateLocalProductOverflowEvent
        t m (levelCutoffTime HLOZPathEvents.upperTailDelta m)
          (sourceCandidateLazyCap48 m) (data.externalThreshold m)) ≠ ∞ := by
    simpa only [← candidateLocalProductOverflowEvent_eq_rankSplit] using
      hoverflowRaw
  have hcandidate :=
    simpleRandomWalk_onTimeCandidateLocalProductBeta_series_ne_top_of_overflow
      t sourceCandidateLazyCap48 data.externalThreshold data.threshold_pos
        hoverflow
  exact simpleRandomWalk_hlozExceptional_series_ne_top_of_candidateLocal
    hProp13 t data.externalThreshold hcandidate hcomplement

/-- Rankwise form of the carrier-independent assembly.  This is the natural
consumer for the three accepted-creation source screens; the finite union is
closed here rather than in the screened-carrier module. -/
theorem simpleRandomWalk_hlozExceptional_series_ne_top_of_balance_rank_source_series
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling)
    (hbalance : ∑' m, simpleRandomWalk
      (candidateLocalProductPositiveInterfaceBalanceRemainderEvent data t m) ≠ ∞)
    (hsourceOne : ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank data t 1 m) ≠ ∞)
    (hsourceTwo : ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank data t 2 m) ≠ ∞)
    (hsourceThree : ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank data t 3 m) ≠ ∞)
    (hcomplement : ∑' m, simpleRandomWalk
      (onTimeProductBetaCandidateLocalComplementEvent t m
        (data.externalThreshold m)) ≠ ∞) :
    ∑' m, simpleRandomWalk (HLOZPathEvents.hlozExceptionalEvent t m) ≠ ∞ := by
  apply simpleRandomWalk_hlozExceptional_series_ne_top_of_balance_source_series
    hProp13 data t hbalance
  · simpa only [candidateLocalProductOrientedSourceEvent] using
      measure_union_series_ne_top hsourceOne
        (measure_union_series_ne_top hsourceTwo hsourceThree)
  · exact hcomplement

end

end Erdos1165.HLOZNoLazyFullGapSeriesAssembly
