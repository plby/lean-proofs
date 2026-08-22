/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongSlotCapCover

/-!
# Finite-delta history summation for physical strong singleton slots

This adapter packages the monotone physical same-cap cover into the existing
honest endpoint-increment history theorem.  External creation trace atoms are
the disjoint global carrier; no unconditional retained-word cylinder is
summed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongHistoryCap

open HLOZCandidateLocalBroadThetaActualDeltaHistoryCap
open HLOZCandidateLocalBroadThetaExternalProduct
open HLOZCandidateLocalBroadThetaStrongSlotCapCover
open HLOZSourceOrientedThetaExternalProduct
open LazyDecomposition TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Countable physical singleton histories with a uniform finite-product
coefficient. -/
structure PhysicalStrongSingletonHistoryData
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
  arithmetic : ∀ history cap,
    ExternalBroadSourceThetaProductArithmetic
      (concreteFiber o m k supportAt supportData (eta history))
      width externalThreshold cap
  cost_le : ∀ history cap,
    ENNReal.ofReal (2 * ∑ c, externalThetaCost
      (concreteFiber o m k supportAt supportData (eta history)) cap c) ≤ ratio
  event_subset : event ⊆ ⋃ history, ⋃ cap,
    physicalSingletonBroadSourceStrongCap supportData (eta history)
      (base history) cap width externalThreshold

namespace PhysicalStrongSingletonHistoryData

/-- Forget the physical presentation and use the honest actual-delta history
summation engine. -/
noncomputable def toBroadSourceActualDeltaHistoryCapData
    {History : Type*} [Countable History]
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {width externalThreshold : ℕ}
    {event : Set WalkPath} {ratio : ℝ≥0∞}
    (hm : 1 < m) (hk : 0 < k)
    (data : PhysicalStrongSingletonHistoryData History t o m k supportAt
      supportData width externalThreshold event ratio) :
    BroadSourceActualDeltaHistoryCapData History t o m k supportAt supportData
      width externalThreshold event ratio where
  eta := data.eta
  eta_injective := data.eta_injective
  supportOfCode := data.supportOfCode
  support_code := data.support_code
  base := data.base
  support_singleton := data.support_singleton
  base_represented := data.base_represented
  fixedPrefix_pos := data.fixedPrefix_pos
  sourceCap := fun history cap ↦
    physicalSingletonBroadSourceStrongCap supportData (data.eta history)
      (data.base history) cap width externalThreshold
  arithmetic := data.arithmetic
  cost_le := data.cost_le
  sourceCap_subset := fun history cap ↦
    physicalSingletonBroadSourceStrongCap_subset_zeroDeltaCap supportData
      (data.eta history) (data.base history)
      (data.support_singleton history) hm hk cap width externalThreshold
  event_subset := data.event_subset
  source_monotone := fun history ↦
    physicalSingletonBroadSourceStrongCap_monotone supportData
      (data.eta history) (data.base history) width externalThreshold

theorem measure_event_le
    {History : Type*} [Countable History]
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {width externalThreshold : ℕ}
    {event : Set WalkPath} {ratio : ℝ≥0∞}
    (hm : 1 < m) (hk : 0 < k)
    (data : PhysicalStrongSingletonHistoryData History t o m k supportAt
      supportData width externalThreshold event ratio) :
    simpleRandomWalk event ≤ 3 * ratio := by
  exact (data.toBroadSourceActualDeltaHistoryCapData hm hk).measure_event_le
    hm hk

end PhysicalStrongSingletonHistoryData

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongHistoryCap
