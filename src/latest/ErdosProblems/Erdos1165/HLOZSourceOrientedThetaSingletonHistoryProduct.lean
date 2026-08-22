/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceSlotCapCover

/-!
# Countable singleton source histories

This module packages the same-cap physical source-slot cover into the finite
actual-endpoint-increment history summation.  Histories are complete external
stopped codes with one represented, orientation-compatible exposed domino.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaSingletonHistoryProduct

open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaHistoryCap
open HLOZSourceOrientedThetaSourceSelectedCarrier
open HLOZSourceOrientedThetaSourceSlotCapCover
open HLOZSourceOrientedThetaWindowSplit
open HLOZThetaSourceBalance
open LazyDecomposition SpatialInsertionFiber
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A complete stopped external history with a unique exposed source base. -/
structure SingletonSourceHistory
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) where
  eta : SupportedIndex t o m k supportAt
  base : Point
  support_singleton : eta.1.2 = {base}
  base_represented : base ∈
    tilingExternalDominoBases t eta.1.1.start eta.1.1.retained
  base_compatible : OrientationCompatible o base
  fixedPrefix_pos : 0 < eta.1.1.initial.1.length +
    2 * eta.1.1.retainedCount + eta.1.1.tail.1.length
  deriving Countable

namespace SingletonSourceHistory

theorem eta_injective
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} :
    Function.Injective
      (SingletonSourceHistory.eta (t := t) (o := o) (m := m) (k := k)
        (supportAt := supportAt)) := by
  intro h h' heta
  cases h with
  | mk eta b hsingle hrepresented hcompatible hpositive =>
    cases h' with
    | mk eta' b' hsingle' hrepresented' hcompatible' hpositive' =>
      dsimp only at heta
      subst eta'
      have hbase : b = b' := by
        simpa only [Finset.singleton_inj] using hsingle.symm.trans hsingle'
      subst b'
      rfl

end SingletonSourceHistory

/-- The literal cofinal product majorant over all singleton stopped
histories. -/
def singletonSourceThetaProductMajorant
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (w externalLow externalHigh : ℕ) : Set WalkPath :=
  ⋃ history : SingletonSourceHistory t o m k supportAt, ⋃ cap : ℕ,
    physicalSingletonSourceThetaCap supportData history.eta history.base cap
      w externalLow externalHigh

/-- Literal finite-product inputs for every complete singleton history. -/
structure SingletonSourceThetaProductData
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (w externalLow externalHigh : ℕ) (ratio : ℝ≥0∞) where
  supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point
  support_code : ∀ s n, supportAt s n = supportOfCode
    (fixedOrientedTypedExternalWordCode t o n s)
  arithmetic : ∀ (history : SingletonSourceHistory t o m k supportAt) cap,
    ExternalThetaProductArithmetic
      (withExternalSourceSelected
        (concreteFiber o m k supportAt supportData history.eta)
          w externalLow externalHigh)
      w externalLow externalHigh cap
  cost_le : ∀ (history : SingletonSourceHistory t o m k supportAt) cap,
    ENNReal.ofReal (2 * ∑ c, externalThetaCost
      (withExternalSourceSelected
        (concreteFiber o m k supportAt supportData history.eta)
          w externalLow externalHigh) cap c) ≤ ratio

namespace SingletonSourceThetaProductData

noncomputable def toHistoryCapData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {w externalLow externalHigh : ℕ} {ratio : ℝ≥0∞}
    (hm : 1 < m) (hk : 0 < k)
    (data : SingletonSourceThetaProductData t o m k supportAt supportData
      w externalLow externalHigh ratio) :
    SourceActualDeltaHistoryCapData
      (SingletonSourceHistory t o m k supportAt) t o m k supportAt supportData
      w externalLow externalHigh
      (singletonSourceThetaProductMajorant t o m k supportAt supportData
        w externalLow externalHigh) ratio where
  eta := SingletonSourceHistory.eta
  eta_injective := SingletonSourceHistory.eta_injective
  supportOfCode := data.supportOfCode
  support_code := data.support_code
  base := SingletonSourceHistory.base
  support_singleton := SingletonSourceHistory.support_singleton
  base_represented := SingletonSourceHistory.base_represented
  base_compatible := SingletonSourceHistory.base_compatible
  fixedPrefix_pos := SingletonSourceHistory.fixedPrefix_pos
  sourceCap := fun history cap ↦ physicalSingletonSourceThetaCap supportData
    history.eta history.base cap w externalLow externalHigh
  sourceCap_vTwo := fun history cap ↦
    physicalSingletonSourceThetaCap_empty_or_vTwo supportData history.eta
      history.base cap w externalLow externalHigh
  arithmetic := data.arithmetic
  cost_le := data.cost_le
  sourceCap_subset := fun history cap ↦
    physicalSingletonSourceThetaCap_subset_sourceThetaCap supportData
      data.supportOfCode data.support_code history.eta history.base
      history.support_singleton hm hk cap w externalLow externalHigh
  event_subset := by
    intro s hs
    exact hs
  source_monotone := fun history ↦
    physicalSingletonSourceThetaCap_monotone supportData history.eta
      history.base w externalLow externalHigh

theorem measure_majorant_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {w externalLow externalHigh : ℕ} {ratio : ℝ≥0∞}
    (hm : 1 < m) (hk : 0 < k)
    (data : SingletonSourceThetaProductData t o m k supportAt supportData
      w externalLow externalHigh ratio) :
    simpleRandomWalk (singletonSourceThetaProductMajorant t o m k supportAt
      supportData w externalLow externalHigh) ≤ 3 * ratio :=
  (data.toHistoryCapData hm hk).measure_event_le hm hk

end SingletonSourceThetaProductData

/-- The physical singleton event before choosing its complete retained
external code. -/
def physicalPositiveSingletonSourceThetaEvent
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (w externalLow externalHigh : ℕ) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    ∃ b, supportAt s (creationTimeNat m k s) = {b} ∧
      (let z := fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k s) s;
        0 < z.initial.1.length + 2 * z.retainedCount + z.tail.1.length) ∧
      b ∈ orientedRestrictedThetaSourceAtCreation
        t o m k w externalLow externalHigh s}

theorem physicalPositiveSingletonSourceThetaEvent_subset_majorant
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (w externalLow externalHigh : ℕ) :
    physicalPositiveSingletonSourceThetaEvent t o m k supportAt w externalLow
        externalHigh ⊆
      singletonSourceThetaProductMajorant t o m k supportAt supportData w
        externalLow externalHigh := by
  classical
  intro s hs
  rcases hs with ⟨hvalid, hreach, b, hsupport, hfixedPos, hbsource⟩
  let z := fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s
  have hatom : s ∈ orientedExternalAllCreationSupportTraceAtom
      t o m k supportAt z {b} := by
    rw [orientedExternalAllCreationSupportTraceAtom_eq]
    exact ⟨hvalid, hreach, rfl, hsupport⟩
  let eta : SupportedIndex t o m k supportAt := ⟨(z, {b}), ⟨s, hatom⟩⟩
  have hbrepresented : b ∈
      tilingExternalDominoBases t eta.1.1.start eta.1.1.retained := by
    have hmem : b ∈ supportAt s (creationTimeNat m k s) := by
      rw [hsupport]
      simp
    simpa only [eta, z] using supportData.represented s
      (creationTimeNat m k s) hvalid hmem
  have hcompat : OrientationCompatible o b := by
    have hbtheta := (Finset.mem_filter.mp hbsource).1
    rw [orientedTilingThetaAtCreation, orientedTilingThetaBases,
      Finset.mem_filter, mem_orientedTilingVTwoBases_iff] at hbtheta
    exact hbtheta.1.2
  let history : SingletonSourceHistory t o m k supportAt :=
    ⟨eta, b, rfl, hbrepresented, hcompat, by
      simpa only [eta, z] using hfixedPos⟩
  have hcomplete :=
    (concreteFiber o m k supportAt supportData eta).atom_complete hatom
  rcases Set.mem_iUnion.mp hcomplete with ⟨cap, hcap⟩
  apply Set.mem_iUnion.mpr
  refine ⟨history, Set.mem_iUnion.mpr ⟨cap, ?_⟩⟩
  exact ⟨by simpa only [sourceSlotAtomCap, history, eta] using hcap, hbsource⟩

end

end Erdos1165.HLOZSourceOrientedThetaSingletonHistoryProduct
