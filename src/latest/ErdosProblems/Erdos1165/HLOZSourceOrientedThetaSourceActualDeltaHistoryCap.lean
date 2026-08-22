/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZFiniteDeltaHistoryCapSummation
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaCapBound

/-!
# Countable source-slot histories with finite actual-rank increments

This is the cofinal/disjoint wrapper around the literal cap-level product.
The history data contain only deterministic stopped-coordinate facts and the
checked finite-product arithmetic.  The resulting object is the generic
finite-delta history certificate, with the common increment type `Fin 3`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaHistoryCap

open HLOZFiniteDeltaHistoryCapSummation
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaCapBound
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition
open PreStoppingFiber SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Deterministic data for a countable family of singleton source-slot
histories.  The coefficient bound is a finite-product estimate in `ENNReal`;
it is not a path-event probability premise. -/
structure SourceActualDeltaHistoryCapData
    (History : Type*) [Countable History]
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (w externalLow externalHigh : ℕ)
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
  base_compatible : ∀ history, OrientationCompatible o (base history)
  fixedPrefix_pos : ∀ history,
    0 < (eta history).1.1.initial.1.length +
      2 * (eta history).1.1.retainedCount +
        (eta history).1.1.tail.1.length
  sourceCap : History → ℕ → Set WalkPath
  sourceCap_vTwo : ∀ history cap, sourceCap history cap = ∅ ∨
    ∃ (q₀ : TilingCappedCoordinates (eta history).1.1.retainedCount
        ((concreteFiber o m k supportAt supportData
          (eta history)).coordinateCap cap)) (window : Finset ℕ),
      let z := (eta history).1.1
      let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start
        z.retained (fun j ↦ (q₀ j : ℕ)) z.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingVTwoAt t window s v.length (base history)
  arithmetic : ∀ history cap,
    ExternalThetaProductArithmetic
      (HLOZSourceOrientedThetaSourceSelectedCarrier.withExternalSourceSelected
        (concreteFiber o m k supportAt supportData (eta history))
          w externalLow externalHigh)
      w externalLow externalHigh cap
  cost_le : ∀ history cap,
    ENNReal.ofReal (2 * ∑ c, externalThetaCost
      (HLOZSourceOrientedThetaSourceSelectedCarrier.withExternalSourceSelected
      (concreteFiber o m k supportAt supportData (eta history))
          w externalLow externalHigh) cap c) ≤ ratio
  sourceCap_subset : ∀ history cap,
    sourceCap history cap ⊆
      sourceThetaCap supportData (eta history) cap w externalLow externalHigh
  event_subset : event ⊆ ⋃ history, ⋃ cap, sourceCap history cap
  source_monotone : ∀ history, Monotone (sourceCap history)

namespace SourceActualDeltaHistoryCapData

private noncomputable def localEquiv
    {History : Type*} [Countable History]
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {w externalLow externalHigh : ℕ}
    {event : Set WalkPath} {ratio : ℝ≥0∞}
    (data : SourceActualDeltaHistoryCapData History t o m k supportAt
      supportData w externalLow externalHigh event ratio)
    (history : History) :
    SourceActualDeltaIndex
        (concreteFiber o m k supportAt supportData (data.eta history)) ≃ Fin 3 :=
  sourceActualDeltaIndexEquivFinThree supportData (data.eta history)
    (data.base history) (data.support_singleton history)
    (data.base_represented history)

/-- The finite-delta history certificate obtained from the literal stopped
products. -/
noncomputable def toFiniteDeltaHistoryCapData
    {History : Type*} [Countable History]
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {w externalLow externalHigh : ℕ}
    {event : Set WalkPath} {ratio : ℝ≥0∞}
    (hm : 1 < m) (hk : 0 < k)
    (data : SourceActualDeltaHistoryCapData History t o m k supportAt
      supportData w externalLow externalHigh event ratio) :
    FiniteDeltaHistoryCapData (History := History) (Delta := Fin 3)
      simpleRandomWalk event ratio where
  sourceCap := fun cap history ↦ data.sourceCap history cap
  rankCap := fun cap delta history ↦
    sourceActualDeltaCap supportData (data.eta history) cap w externalLow
      externalHigh ((data.localEquiv history).symm delta)
  rankAtom := fun delta history ↦
    TilingOrientedExternalStaticDStoppedCoordinate.orientedExternalOnlyCreationTraceAtom
      t o m (k + (delta : ℕ)) (data.eta history).1.1
  event_subset := data.event_subset
  source_monotone := data.source_monotone
  cap_le := by
    intro cap history
    rcases data.sourceCap_vTwo history cap with hempty | ⟨q₀, window, hVTwo⟩
    · rw [hempty, measure_empty]
      exact bot_le
    let e := data.localEquiv history
    let localRatio := ENNReal.ofReal (2 * ∑ c, externalThetaCost
      (HLOZSourceOrientedThetaSourceSelectedCarrier.withExternalSourceSelected
        (concreteFiber o m k supportAt supportData (data.eta history))
          w externalLow externalHigh) cap c)
    have hlocal := simpleRandomWalk_sourceThetaCap_le_actualDelta_sum
      supportData (data.eta history) hm hk (data.fixedPrefix_pos history)
      cap w externalLow externalHigh (data.arithmetic history cap)
      (data.base history) (data.support_singleton history)
      (data.base_represented history) (data.base_compatible history)
      q₀ window hVTwo
    have hsum :
        (∑' delta : SourceActualDeltaIndex
            (concreteFiber o m k supportAt supportData (data.eta history)),
          simpleRandomWalk (sourceActualDeltaCap supportData (data.eta history)
            cap w externalLow externalHigh delta)) =
        ∑' delta : Fin 3,
          simpleRandomWalk (sourceActualDeltaCap supportData (data.eta history)
            cap w externalLow externalHigh (e.symm delta)) := by
      exact (e.symm.tsum_eq (fun delta : SourceActualDeltaIndex
          (concreteFiber o m k supportAt supportData (data.eta history)) ↦
        simpleRandomWalk
        (sourceActualDeltaCap supportData (data.eta history) cap w externalLow
          externalHigh delta))).symm
    rw [hsum] at hlocal
    exact (measure_mono (data.sourceCap_subset history cap)).trans <|
      hlocal.trans (mul_le_mul_of_nonneg_right
      (data.cost_le history cap) bot_le)
  measurable_rankCap := by
    intro cap delta history
    exact measurableSet_sourceActualDeltaCap supportData (data.eta history)
      cap w externalLow externalHigh ((data.localEquiv history).symm delta)
  rankCap_subset_rankAtom := by
    intro cap delta history
    have hsubset := sourceActualDeltaCap_subset_externalOnlyCreationTraceAtom
      supportData (data.eta history) hm hk cap w externalLow externalHigh
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

/-- Global source-slot estimate after cofinal cap removal and the disjoint
history sum.  The factor three is the exact endpoint-increment multiplicity
of one exposed domino. -/
theorem measure_event_le
    {History : Type*} [Countable History]
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {w externalLow externalHigh : ℕ}
    {event : Set WalkPath} {ratio : ℝ≥0∞}
    (hm : 1 < m) (hk : 0 < k)
    (data : SourceActualDeltaHistoryCapData History t o m k supportAt
      supportData w externalLow externalHigh event ratio) :
    simpleRandomWalk event ≤ 3 * ratio := by
  simpa using (data.toFiniteDeltaHistoryCapData hm hk).measure_event_le
    simpleRandomWalk event ratio

end SourceActualDeltaHistoryCapData

end

end Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaHistoryCap
