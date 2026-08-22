/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZFiniteDeltaHistoryCapSummation
import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaWalkCap

/-!
# Countable broad-Theta histories with honest endpoint increments

This is the cofinal/disjoint history wrapper for the one-sided candidate-local
Theta screen.  Each replacement cap stops at its literal endpoint-count
increment.  Complete external creation atoms provide the disjoint global
carrier; no unconditional retained-word cylinder is summed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaHistoryCap

open HLOZCandidateLocalBroadThetaActualDeltaSelected
open HLOZCandidateLocalBroadThetaActualDeltaProduct
open HLOZCandidateLocalBroadThetaActualDeltaWalkCap
open HLOZCandidateLocalBroadThetaExternalProduct
open HLOZFiniteDeltaHistoryCapSummation
open HLOZPathEvents
open HLOZSourceOrientedThetaAcceptedCreationPath
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaCapBound
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PathInsertion PreStoppingFiber SpatialInsertionFiber
open StoppedInsertion TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedExternalStaticDStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber TilingVariableStoppedTracePartition
open TilingDistinguishedTraceInvariant
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Every broad actual-increment cap belongs to the complete external-word
creation atom at its honest raised rank. -/
theorem broadSourceActualDeltaCap_subset_externalOnlyCreationTraceAtom
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k)
    (cap width externalThreshold : ℕ)
    (delta : SourceActualDeltaIndex
      (concreteFiber o m k supportAt supportData eta)) :
    broadSourceActualDeltaCap supportData eta cap width externalThreshold delta ⊆
      orientedExternalOnlyCreationTraceAtom t o m (k + (delta : ℕ))
        eta.1.1 := by
  classical
  intro s hs
  rcases hs with ⟨hvalid, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨q, hq⟩
  let data := concreteFiber o m k supportAt supportData eta
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  have hlt : v.length <
      externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    let dummy : TilingCreationFavoriteData :=
      ((∅, ∅), (eta.1.1.start, eta.1.1.start))
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) q.1
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hcreationQ : ThresholdCreation sq m (k + (delta : ℕ)) v.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
      v.length _ hlt).mp
    exact q.2.2
  have hp : pathPrefix s v.length = pathPrefix sq v.length := by
    have hp' := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
      eta.1.1.initial.1 eta.1.1.start eta.1.1.retained
      (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1 (stepsOfWalk s) hq
    change trajectory (stepsOfWalk s) = s at hvalid
    rw [hvalid] at hp'
    simpa only [sq, v] using hp'
  have hcreationS : ThresholdCreation s m (k + (delta : ℕ)) v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp
      (Nat.le_refl v.length)).mpr hcreationQ
  have htime : creationTimeNat m (k + (delta : ℕ)) s = v.length :=
    creationTimeNat_eq_of_creation hcreationS
  have heta_nonempty :
      (allRepresentedExternalCreationTraceAtom t o m k eta.1.1).Nonempty := by
    rcases eta.2 with ⟨s₀, hs₀⟩
    rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs₀
    exact ⟨s₀, hs₀.1, hs₀.2.1, hs₀.2.2.1⟩
  let etaAll : TilingOrientedAllRepresentedExternalFiber.SupportedIndex
      t o m k := ⟨eta.1.1, heta_nonempty⟩
  have hcodeQ : fixedOrientedTypedExternalWordCode t o v.length sq =
      eta.1.1 := by
    simpa only [etaAll, sq, v] using
      (fixedCode_prefixedInsertion etaAll hm hk
        (fun j ↦ (q.1 j : ℕ)))
  have hcodeS : fixedOrientedTypedExternalWordCode t o v.length s =
      eta.1.1 :=
    (fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp).trans hcodeQ
  refine ⟨hvalid, ⟨v.length, hcreationS.1⟩, ?_⟩
  rw [htime]
  exact hcodeS

/-- Deterministic data for a countable family of broad one-sided stopped
histories.  The only quantitative field is a checked finite-product
coefficient bound. -/
structure BroadSourceActualDeltaHistoryCapData
    (History : Type*) [Countable History]
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (width externalThreshold : ℕ)
    (event : Set WalkPath) (ratio : ℝ≥0∞) where
  eta : History → SupportedIndex t o m k supportAt
  eta_injective : Function.Injective eta
  supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point
  support_code : ∀ s n, supportAt s n = supportOfCode
    (fixedOrientedTypedExternalWordCode t o n s)
  base : History → Point
  support_singleton : ∀ history, (eta history).1.2 = {base history}
  base_represented : ∀ history, base history ∈
    tilingExternalDominoBases t (eta history).1.1.start
      (eta history).1.1.retained
  fixedPrefix_pos : ∀ history,
    0 < (eta history).1.1.initial.1.length +
      2 * (eta history).1.1.retainedCount +
        (eta history).1.1.tail.1.length
  sourceCap : History → ℕ → Set WalkPath
  arithmetic : ∀ history cap,
    ExternalBroadSourceThetaProductArithmetic
      (concreteFiber o m k supportAt supportData (eta history))
      width externalThreshold cap
  cost_le : ∀ history cap,
    ENNReal.ofReal (2 * ∑ c, externalThetaCost
      (concreteFiber o m k supportAt supportData (eta history)) cap c) ≤ ratio
  sourceCap_subset : ∀ history cap,
    sourceCap history cap ⊆ broadSourceZeroDeltaCap supportData
      (eta history) cap width externalThreshold
  event_subset : event ⊆ ⋃ history, ⋃ cap, sourceCap history cap
  source_monotone : ∀ history, Monotone (sourceCap history)

namespace BroadSourceActualDeltaHistoryCapData

private noncomputable def localEquiv
    {History : Type*} [Countable History]
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {width externalThreshold : ℕ}
    {event : Set WalkPath} {ratio : ℝ≥0∞}
    (data : BroadSourceActualDeltaHistoryCapData History t o m k supportAt
      supportData width externalThreshold event ratio)
    (history : History) :
    SourceActualDeltaIndex
        (concreteFiber o m k supportAt supportData (data.eta history)) ≃ Fin 3 :=
  sourceActualDeltaIndexEquivFinThree supportData (data.eta history)
    (data.base history) (data.support_singleton history)
    (data.base_represented history)

noncomputable def toFiniteDeltaHistoryCapData
    {History : Type*} [Countable History]
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {width externalThreshold : ℕ}
    {event : Set WalkPath} {ratio : ℝ≥0∞}
    (hm : 1 < m) (hk : 0 < k)
    (data : BroadSourceActualDeltaHistoryCapData History t o m k supportAt
      supportData width externalThreshold event ratio) :
    FiniteDeltaHistoryCapData (History := History) (Delta := Fin 3)
      simpleRandomWalk event ratio where
  sourceCap := fun cap history ↦ data.sourceCap history cap
  rankCap := fun cap delta history ↦ broadSourceActualDeltaCap supportData
    (data.eta history) cap width externalThreshold
      ((data.localEquiv history).symm delta)
  rankAtom := fun delta history ↦
    orientedExternalOnlyCreationTraceAtom t o m (k + (delta : ℕ))
      (data.eta history).1.1
  event_subset := data.event_subset
  source_monotone := data.source_monotone
  cap_le := by
    intro cap history
    let e := data.localEquiv history
    have hlocal := simpleRandomWalk_broadSourceZeroDeltaCap_le_actualDelta_sum
      supportData (data.eta history) (by omega) hk
        (data.fixedPrefix_pos history)
      cap width externalThreshold (data.arithmetic history cap)
    have hsum :
        (∑' delta : SourceActualDeltaIndex
            (concreteFiber o m k supportAt supportData (data.eta history)),
          simpleRandomWalk (broadSourceActualDeltaCap supportData
            (data.eta history) cap width externalThreshold delta)) =
        ∑' delta : Fin 3,
          simpleRandomWalk (broadSourceActualDeltaCap supportData
            (data.eta history) cap width externalThreshold (e.symm delta)) := by
      exact (e.symm.tsum_eq (fun delta : SourceActualDeltaIndex
          (concreteFiber o m k supportAt supportData (data.eta history)) ↦
        simpleRandomWalk (broadSourceActualDeltaCap supportData
          (data.eta history) cap width externalThreshold delta))).symm
    rw [hsum] at hlocal
    exact (measure_mono (data.sourceCap_subset history cap)).trans <|
      hlocal.trans (mul_le_mul_of_nonneg_right
        (data.cost_le history cap) bot_le)
  measurable_rankCap := by
    intro cap delta history
    exact measurableSet_broadSourceActualDeltaCap supportData
      (data.eta history) cap width externalThreshold
        ((data.localEquiv history).symm delta)
  rankCap_subset_rankAtom := by
    intro cap delta history
    have hsubset :=
      broadSourceActualDeltaCap_subset_externalOnlyCreationTraceAtom
        supportData (data.eta history) hm hk cap width externalThreshold
          ((data.localEquiv history).symm delta)
    simpa only [localEquiv,
      sourceActualDeltaIndexEquivFinThree_symm_val] using hsubset
  disjoint_rankAtom := by
    intro delta history history' hne
    have heta : data.eta history ≠ data.eta history' := by
      intro heq
      exact hne (data.eta_injective heq)
    exact pairwise_disjoint_externalOnlyCreationTraceAtom
      data.supportOfCode data.support_code (k + (delta : ℕ)) heta

theorem measure_event_le
    {History : Type*} [Countable History]
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {width externalThreshold : ℕ}
    {event : Set WalkPath} {ratio : ℝ≥0∞}
    (hm : 1 < m) (hk : 0 < k)
    (data : BroadSourceActualDeltaHistoryCapData History t o m k supportAt
      supportData width externalThreshold event ratio) :
    simpleRandomWalk event ≤ 3 * ratio := by
  simpa using (data.toFiniteDeltaHistoryCapData hm hk).measure_event_le
    simpleRandomWalk event ratio

end BroadSourceActualDeltaHistoryCapData

end

end Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaHistoryCap
