/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaZeroPrefixOrigin

/-!
# Complete source-window oriented-Theta payment

The positive deleted-prefix product payment and the exceptional zero-prefix
origin payment form a single physical majorant.  This module packages their
pathwise cover and summability without exposing either coordinate carrier.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaSourcePaymentSeries

open ExternalProposition44 HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaPositiveSourcePayment
open HLOZSourceOrientedThetaWindowSplit
open HLOZSourceOrientedThetaZeroPrefixOrigin
open HLOZThetaSourceBalance
open LazyDecomposition VariableStoppedTracePartition
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The physical on-time restricted source-window Theta event, before it is
covered by the two product payments below. -/
def restrictedThetaSourceOnTimeEvent
    (t : DominoTiling) (o : Orientation) (m k : ℕ) : Set WalkPath :=
  {s | ReachesThreshold s m k ∧
    creationTimeNat m k s ≤ hlozCutoff44 m ∧
    (orientedRestrictedThetaSourceAtCreation t o m k
      (shellWidth48 m) (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m) s).Nonempty}

private theorem restrictedThetaSourceAtCreation_eq_inter
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) (s : WalkPath) :
    orientedRestrictedThetaSourceAtCreation t o m k w externalLow
        externalHigh s =
      orientedTilingThetaAtCreation t o m k w externalLow externalHigh s ∩
        orientedTilingVTwoAtCreation t o m k w s := by
  classical
  ext b
  simp only [orientedRestrictedThetaSourceAtCreation, Finset.mem_filter,
    Finset.mem_inter]
  constructor
  · rintro ⟨hbtheta, hbwindow⟩
    refine ⟨hbtheta, ?_⟩
    rw [orientedTilingVTwoAtCreation,
      mem_orientedTilingVTwoBases_iff]
    rw [orientedTilingThetaAtCreation, orientedTilingThetaBases,
      Finset.mem_filter, mem_orientedTilingVTwoBases_iff] at hbtheta
    refine ⟨?_, hbtheta.1.2⟩
    rw [tilingVTwoBases, Finset.mem_filter] at hbtheta ⊢
    exact ⟨hbtheta.1.1.1, hbtheta.1.1.2.1, hbwindow⟩
  · rintro ⟨hbtheta, hbsource⟩
    refine ⟨hbtheta, ?_⟩
    rw [orientedTilingVTwoAtCreation,
      mem_orientedTilingVTwoBases_iff] at hbsource
    rw [tilingVTwoBases, Finset.mem_filter] at hbsource
    exact hbsource.1.2.2

theorem measurable_orientedRestrictedThetaSourceAtCreation
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) :
    Measurable (orientedRestrictedThetaSourceAtCreation t o m k w
      externalLow externalHigh) := by
  rw [show orientedRestrictedThetaSourceAtCreation t o m k w externalLow
      externalHigh = fun s ↦
        orientedTilingThetaAtCreation t o m k w externalLow externalHigh s ∩
          orientedTilingVTwoAtCreation t o m k w s by
    funext s
    exact restrictedThetaSourceAtCreation_eq_inter
      t o m k w externalLow externalHigh s]
  exact (measurable_of_countable
    (fun pair : Finset Point × Finset Point ↦ pair.1 ∩ pair.2)).comp
      ((measurable_orientedTilingThetaAtCreation t o m k w externalLow
        externalHigh).prodMk
        (measurable_orientedTilingVTwoAtCreation t o m k w))

theorem measurableSet_restrictedThetaSourceOnTimeEvent
    (t : DominoTiling) (o : Orientation) (m k : ℕ) :
    MeasurableSet (restrictedThetaSourceOnTimeEvent t o m k) := by
  have hnonempty : MeasurableSet {s : WalkPath |
      (orientedRestrictedThetaSourceAtCreation t o m k
        (shellWidth48 m) (shellZeroExternalLow48 m)
          (shellZeroExternalHigh48 m) s).Nonempty} := by
    have heq : MeasurableSet {s : WalkPath |
        orientedRestrictedThetaSourceAtCreation t o m k
          (shellWidth48 m) (shellZeroExternalLow48 m)
            (shellZeroExternalHigh48 m) s = ∅} :=
      measurableSet_eq_fun
        (measurable_orientedRestrictedThetaSourceAtCreation t o m k
          (shellWidth48 m) (shellZeroExternalLow48 m)
            (shellZeroExternalHigh48 m))
        (g := fun _ ↦ (∅ : Finset Point)) measurable_const
    rw [show {s : WalkPath |
        (orientedRestrictedThetaSourceAtCreation t o m k
          (shellWidth48 m) (shellZeroExternalLow48 m)
            (shellZeroExternalHigh48 m) s).Nonempty} =
        {s : WalkPath |
          orientedRestrictedThetaSourceAtCreation t o m k
            (shellWidth48 m) (shellZeroExternalLow48 m)
              (shellZeroExternalHigh48 m) s = ∅}ᶜ by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff,
        Finset.nonempty_iff_ne_empty]]
    exact heq.compl
  exact (measurableSet_thresholdReachStage m k).inter
    ((measurableSet_le (measurable_creationTimeNat m k) measurable_const).inter
      hnonempty)

/-- Complete payment for a nonempty restricted source-window oriented-Theta
screen at an on-time rank creation. -/
def restrictedThetaSourcePaidEvent
    (t : DominoTiling) (o : Orientation) (m k : ℕ) : Set WalkPath :=
  positiveRestrictedThetaSourceProductMajorant t o m k ∪
    zeroPrefixRestrictedThetaSourceEvent t o m k

theorem restrictedThetaSource_onTime_subset_paid
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (hk : 0 < k) :
    restrictedThetaSourceOnTimeEvent t o m k ⊆
      restrictedThetaSourcePaidEvent t o m k := by
  intro s hs
  have hm : 1 < m := by
    rcases hs.2.2 with ⟨b, hb⟩
    have hbwindow := (Finset.mem_filter.mp hb).2
    simp only [mem_shellZeroSourceTotalWindow] at hbwindow
    omega
  exact restrictedThetaSource_onTime_subset_positive_or_zero
    t o m k hm hk hs

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

theorem simpleRandomWalk_restrictedThetaSourcePaidEvent_series_ne_top
    (t : DominoTiling) (o : Orientation) (k : ℕ) (hk : 0 < k) :
    ∑' m, simpleRandomWalk (restrictedThetaSourcePaidEvent t o m k) ≠ ∞ :=
  measure_union_series_ne_top
    (simpleRandomWalk_positiveSourceProductMajorant_series_ne_top t o k hk)
    (simpleRandomWalk_zeroPrefixRestrictedThetaSourceEvent_series_ne_top
      t o k hk)

theorem simpleRandomWalk_restrictedThetaSourceOnTimeEvent_series_ne_top
    (t : DominoTiling) (o : Orientation) (k : ℕ) (hk : 0 < k) :
    ∑' m, simpleRandomWalk
      (restrictedThetaSourceOnTimeEvent t o m k) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (simpleRandomWalk_restrictedThetaSourcePaidEvent_series_ne_top t o k hk)
  apply ENNReal.tsum_le_tsum
  intro m
  exact measure_mono (restrictedThetaSource_onTime_subset_paid t o m k hk)

end

end Erdos1165.HLOZSourceOrientedThetaSourcePaymentSeries
