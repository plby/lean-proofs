/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZAllTilingSourceTransportScreen
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourcePaymentSeries

/-!
# Transported oriented source-Theta payments

Every row of the finite endpoint table pulls the physical on-time restricted
Theta event back along its law-preserving path map.  This file records the
measure transport and the target-side source-or-Theta dichotomy once, before
the checker and column geometry are instantiated.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaTransportPayment

open ExternalProposition44 HLOZAllTilingSourceTransportScreen
open HLOZGapRandomClockScreen
open HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceEndpointTransportTable
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaSourcePaymentSeries
open HLOZSourceOrientedThetaWindowSplit
open HLOZThetaSourceBalance LazyDecomposition
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Pullback of the physical restricted source-window Theta event along one
row of the finite endpoint transport table. -/
def transportedRestrictedThetaSourceOnTimeEvent
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) : Set WalkPath :=
  sourceTransportPath t cls ⁻¹'
    restrictedThetaSourceOnTimeEvent
      (sourceTransportTargetTiling t cls)
      (sourceTransportTargetOrientation t o cls) m k

theorem measurableSet_transportedRestrictedThetaSourceOnTimeEvent
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) :
    MeasurableSet
      (transportedRestrictedThetaSourceOnTimeEvent t o cls m k) :=
  (measurableSet_restrictedThetaSourceOnTimeEvent
    (sourceTransportTargetTiling t cls)
    (sourceTransportTargetOrientation t o cls) m k).preimage
      (measurable_sourceTransportPath t cls)

theorem simpleRandomWalk_transportedRestrictedThetaSourceOnTimeEvent
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) :
    simpleRandomWalk
        (transportedRestrictedThetaSourceOnTimeEvent t o cls m k) =
      simpleRandomWalk
        (restrictedThetaSourceOnTimeEvent
          (sourceTransportTargetTiling t cls)
          (sourceTransportTargetOrientation t o cls) m k) := by
  exact simpleRandomWalk_preimage_sourceTransportPath t cls
    (measurableSet_restrictedThetaSourceOnTimeEvent
      (sourceTransportTargetTiling t cls)
      (sourceTransportTargetOrientation t o cls) m k)

theorem simpleRandomWalk_transportedRestrictedThetaSourceOnTimeEvent_series_ne_top
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (k : ℕ) (hk : 0 < k) :
    ∑' m, simpleRandomWalk
      (transportedRestrictedThetaSourceOnTimeEvent t o cls m k) ≠ ∞ := by
  simpa only [simpleRandomWalk_transportedRestrictedThetaSourceOnTimeEvent]
    using simpleRandomWalk_restrictedThetaSourceOnTimeEvent_series_ne_top
      (sourceTransportTargetTiling t cls)
      (sourceTransportTargetOrientation t o cls) k hk

/-- Target-side dichotomy.  Once the transported path has the genuine source
profile and enough oriented source-window V2 bases, it lies either in the
literal transported shell source or in the transported restricted-Theta
payment.  The no-next-level condition rules out the replacement window. -/
theorem mem_transportedBandSource_or_restrictedTheta
    {t : DominoTiling} {o : Orientation} {cls : DominantEndpointClass}
    {m k : ℕ} {band : RandomClockBand} {s : WalkPath}
    (hreach : ReachesThreshold (sourceTransportPath t cls s) m k)
    (hrank : band.oldRank = k)
    (hclock : creationTimeNat m k (sourceTransportPath t cls s) ≤
      hlozCutoff44 m)
    (hD : tilingDEtaAtCreation (sourceTransportTargetTiling t cls)
      m k (shellWidth48 m) (m - shellWidth48 m)
        (sourceTransportPath t cls s))
    (hnext : thresholdCount (sourceTransportPath t cls s)
      (creationTimeNat m k (sourceTransportPath t cls s)) (m + 1) = 0)
    (hcard : orientedSourceCut48 m <
      (orientedTilingVTwoAtCreation
        (sourceTransportTargetTiling t cls)
        (sourceTransportTargetOrientation t o cls)
        m k (shellWidth48 m) (sourceTransportPath t cls s)).card) :
    s ∈ transportedBandSourceEvent t o cls m band ∪
      transportedRestrictedThetaSourceOnTimeEvent t o cls m k := by
  classical
  let target := sourceTransportPath t cls s
  let targetTiling := sourceTransportTargetTiling t cls
  let targetOrientation := sourceTransportTargetOrientation t o cls
  by_cases htheta : orientedTilingThetaAtCreation targetTiling
      targetOrientation m k (shellWidth48 m) (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m) target = ∅
  · left
    change target ∈ orientedShellZeroSourceEvent targetTiling
      targetOrientation m band.oldRank (shellWidth48 m)
        (m - shellWidth48 m) (shellZeroExternalLow48 m)
          (shellZeroExternalHigh48 m) (orientedSourceCut48 m)
    subst k
    exact ⟨hreach, hD, htheta, hcard⟩
  · right
    change target ∈ restrictedThetaSourceOnTimeEvent targetTiling
      targetOrientation m k
    refine ⟨hreach, hclock, ?_⟩
    rw [Finset.nonempty_iff_ne_empty]
    intro hsourceEmpty
    apply htheta
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hbtheta
    have hbSupport := (Finset.mem_filter.mp hbtheta).1
    rw [mem_orientedTilingVTwoBases_iff] at hbSupport
    rw [tilingVTwoBases, Finset.mem_filter] at hbSupport
    unfold tilingVTwoAt at hbSupport
    have hbSource : localTime target (creationTimeNat m k target) b ∈
        shellZeroSourceTotalWindow m (shellWidth48 m) := by
      rw [Finset.mem_union] at hbSupport
      rcases hbSupport.1.2.2 with hsource | hreplacement
      · exact hsource
      · have hlt := (thresholdCount_eq_zero_iff_forall_lt target
          (creationTimeNat m k target) (m + 1) (by omega)).mp hnext b
        have hge := (mem_shellZeroReplacementTotalWindow.mp hreplacement).1
        omega
    have hbFiltered : b ∈ orientedRestrictedThetaSourceAtCreation
        targetTiling targetOrientation m k (shellWidth48 m)
          (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) target :=
      Finset.mem_filter.mpr ⟨hbtheta, hbSource⟩
    rw [hsourceEmpty] at hbFiltered
    simp at hbFiltered

end

end Erdos1165.HLOZSourceOrientedThetaTransportPayment
