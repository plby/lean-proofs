/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongHistoryCap
import ErdosProblems.Erdos1165.HLOZConcreteFullBetaProductData
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaLowSingletonProduct

/-!
# Scale-specialized strong broad-source singleton products

The exposed support is one represented domino.  The broad source window uses
the concrete half-level external threshold.  High slots pay the usual
`m^(1-2κ₁)` plus low cost; filtered low slots pay only the stronger
`sqrt m` cost.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongSingletonProduct

open ExternalProposition44
open HLOZCandidateLocalBroadThetaExternalProduct
open HLOZCandidateLocalBroadThetaProduct
open HLOZCandidateLocalBroadThetaStrongHistoryCap
open HLOZCandidateLocalBroadThetaStrongSlotCapCover
open HLOZConcreteFullBetaProductData
open HLOZShellZeroReplacementWindows
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaLowSlotSupport
open HLOZSourceOrientedThetaSingletonHistoryProduct
open HLOZSourceOrientedThetaSingletonScaleProduct
open HLOZSourceOrientedThetaProduct
open LazyDecomposition ScreeningInstantiation
open TilingCappedMarginalization TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def broadStrongSingletonRatio (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 *
    (Real.exp (-17 * balanceRateScale m) +
      Real.exp (-17 * thetaLowRateScale m)))

def broadStrongLowSingletonRatio (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.exp (-17 * thetaLowRateScale m))

/-- Concrete-fibre arithmetic for the broad source window. -/
theorem externalBroadSourceArithmetic_of_scale
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt) (cap : ℕ)
    (scale : CandidateLocalBroadThetaScaleArithmetic m)
    (capacity : HLOZCandidateLocalLazyCap.sourceCandidateLazyCap48 m +
      concreteExternalThreshold48 m + candidateLocalBroadWidth48 m ≤ m + 1) :
    ExternalBroadSourceThetaProductArithmetic
      (concreteFiber o m k supportAt supportData eta)
      (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m) cap := by
  let data := concreteFiber o m k supportAt supportData eta
  refine
    { level_pos := scale.level_pos
      width_bound := scale.width
      capacity := capacity
      margin := scale.margin
      geometric := scale.geometric
      theta := scale.theta
      thick_nonneg := scale.thick_nonneg
      low_dom := scale.low_dom
      upper_le_cap := ?_
      mean := ?_
      window_upper := ?_
      window_cap := ?_ }
  · intro b
    dsimp only [data, concreteFiber]
    omega
  · intro b
    have hcard := card_tilingCoordinatesAt_le_retainedCount_succ t
      eta.1.1.start eta.1.1.retained b.1
    dsimp only [data, concreteFiber] at hcard ⊢
    omega
  · intro b v hv
    simp only [mem_shellZeroSourceFailureWindow] at hv
    dsimp only [data, concreteFiber]
    omega
  · intro b v hv
    simp only [mem_shellZeroSourceFailureWindow] at hv
    dsimp only [data, concreteFiber]
    omega

/-- Uniform high-plus-low cost for one singleton support. -/
theorem broadStrongSingleton_cost_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (history : SingletonSourceHistory t o m k supportAt) (cap : ℕ) :
    ENNReal.ofReal (2 * ∑ c, externalThetaCost
      (concreteFiber o m k supportAt supportData history.eta) cap c) ≤
      broadStrongSingletonRatio m := by
  let data := concreteFiber o m k supportAt supportData history.eta
  have hhigh : (externalThetaHighCoordinates data cap).card ≤ 1 := by
    calc
      (externalThetaHighCoordinates data cap).card ≤
          Fintype.card (TilingAwayDomino t history.eta.1.1.start
            history.eta.1.1.retained
            (supportComplementDistinguished t history.eta.1.1.start
              history.eta.1.1.retained history.eta.1.2)) :=
        Finset.card_le_univ _
      _ = history.eta.1.2.card := by
        rw [Fintype.card_congr (supportAwayEquiv t history.eta.1.1.start
          history.eta.1.1.retained history.eta.1.2
          data.support_represented)]
        exact Fintype.card_coe history.eta.1.2
      _ = 1 := by rw [history.support_singleton]; simp
  have hsum := sum_externalThetaCost_le data cap
  have hreal : 2 * ∑ c, externalThetaCost data cap c ≤
      2 * (Real.exp (-17 * balanceRateScale m) +
        Real.exp (-17 * thetaLowRateScale m)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      (∑ c, externalThetaCost data cap c) ≤
          ((externalThetaHighCoordinates data cap).card : ℝ) *
              Real.exp (-17 * balanceRateScale m) +
            (history.eta.1.2.card : ℝ) *
              Real.exp (-17 * thetaLowRateScale m) := hsum
      _ ≤ 1 * Real.exp (-17 * balanceRateScale m) +
            1 * Real.exp (-17 * thetaLowRateScale m) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hhigh)
            (Real.exp_pos _).le
        · rw [history.support_singleton]
          simp
      _ = _ := by ring
  exact ENNReal.ofReal_le_ofReal hreal

private theorem history_base_mem_supportOfCode
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point)
    (support_code : ∀ s n, supportAt s n = supportOfCode
      (fixedOrientedTypedExternalWordCode t o n s))
    (history : SingletonSourceHistory t o m k supportAt) :
    history.base ∈ supportOfCode history.eta.1.1 := by
  rcases history.eta.2 with ⟨s, hs⟩
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
  have hb : history.base ∈ supportAt s (creationTimeNat m k s) := by
    rw [hs.2.2.2, history.support_singleton]
    simp
  rw [support_code, hs.2.2.1] at hb
  exact hb

private theorem broad_low_history_highCoordinates_eq_empty
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {slot : Fin (hlozCutoff44 m + 1)}
    (history : SingletonSourceHistory t o m k
      (lowFilteredSlotSupportAt t o m slot)) (cap : ℕ) :
    externalThetaHighCoordinates
      (concreteFiber o m k (lowFilteredSlotSupportAt t o m slot)
        (lowFilteredSlotSupportData t o m k slot) history.eta) cap = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  rw [externalThetaHighCoordinates, Finset.mem_filter] at hc
  have hcS := (away_mem_support_iff t history.eta.1.1.start
    history.eta.1.1.retained history.eta.1.2 c.1).1 c.2
  have hcPoint : c.1.1 = history.base := by
    have : c.1.1 ∈ ({history.base} : Finset Point) := by
      simpa only [← history.support_singleton] using hcS
    simpa only [Finset.mem_singleton] using this
  have hbaseLow := externalCount_lt_of_mem_lowFilteredSlotSupportOfCode
    (history_base_mem_supportOfCode
      (lowFilteredSlotSupportOfCode t o m slot) (fun _ _ ↦ rfl) history)
  have hrepresented : history.base ∈ tilingExternalDominoBases t
      history.eta.1.1.start history.eta.1.1.retained :=
    history.base_represented
  have hbaseLow' : Fintype.card (TilingCoordinatesAt t
      history.eta.1.1.start history.eta.1.1.retained
      ⟨history.base, hrepresented⟩) < hlozThickLevel44 m := by
    simpa [HLOZSourceOrientedThetaCreationSlots.orientedThetaCodeExternalCount,
      hrepresented] using hbaseLow
  have heq : c.1 = ⟨history.base, hrepresented⟩ := by
    apply Subtype.ext
    exact hcPoint
  rw [heq] at hc
  omega

theorem broadStrongLowSingleton_cost_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {slot : Fin (hlozCutoff44 m + 1)}
    (history : SingletonSourceHistory t o m k
      (lowFilteredSlotSupportAt t o m slot)) (cap : ℕ) :
    ENNReal.ofReal (2 * ∑ c, externalThetaCost
      (concreteFiber o m k (lowFilteredSlotSupportAt t o m slot)
        (lowFilteredSlotSupportData t o m k slot) history.eta) cap c) ≤
      broadStrongLowSingletonRatio m := by
  let data := concreteFiber o m k (lowFilteredSlotSupportAt t o m slot)
    (lowFilteredSlotSupportData t o m k slot) history.eta
  have hsum := sum_externalThetaCost_le data cap
  have hzero := broad_low_history_highCoordinates_eq_empty history cap
  have hreal : 2 * ∑ c, externalThetaCost data cap c ≤
      2 * Real.exp (-17 * thetaLowRateScale m) := by
    calc
      2 * ∑ c, externalThetaCost data cap c ≤
          2 * (((externalThetaHighCoordinates data cap).card : ℝ) *
              Real.exp (-17 * balanceRateScale m) +
            (history.eta.1.2.card : ℝ) *
              Real.exp (-17 * thetaLowRateScale m)) := by gcongr
      _ = 2 * Real.exp (-17 * thetaLowRateScale m) := by
        rw [hzero, history.support_singleton]
        simp
  exact ENNReal.ofReal_le_ofReal hreal

/-- Cofinal physical strong source product over every complete singleton
external history. -/
def physicalBroadStrongSingletonMajorant
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (width externalThreshold : ℕ) : Set WalkPath :=
  ⋃ history : SingletonSourceHistory t o m k supportAt, ⋃ cap : ℕ,
    physicalSingletonBroadSourceStrongCap supportData history.eta history.base
      cap width externalThreshold

/-- Uniform product inputs for the physical strong singleton histories. -/
structure PhysicalBroadStrongSingletonProductData
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (width externalThreshold : ℕ) (ratio : ℝ≥0∞) where
  supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point
  support_code : ∀ s n, supportAt s n = supportOfCode
    (fixedOrientedTypedExternalWordCode t o n s)
  arithmetic : ∀ (history : SingletonSourceHistory t o m k supportAt) cap,
    ExternalBroadSourceThetaProductArithmetic
      (concreteFiber o m k supportAt supportData history.eta)
      width externalThreshold cap
  cost_le : ∀ (history : SingletonSourceHistory t o m k supportAt) cap,
    ENNReal.ofReal (2 * ∑ c, externalThetaCost
      (concreteFiber o m k supportAt supportData history.eta) cap c) ≤ ratio

namespace PhysicalBroadStrongSingletonProductData

noncomputable def toHistoryData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {width externalThreshold : ℕ} {ratio : ℝ≥0∞}
    (data : PhysicalBroadStrongSingletonProductData t o m k supportAt
      supportData width externalThreshold ratio) :
    PhysicalStrongSingletonHistoryData
      (SingletonSourceHistory t o m k supportAt) t o m k supportAt supportData
      width externalThreshold
      (physicalBroadStrongSingletonMajorant t o m k supportAt supportData
        width externalThreshold) ratio where
  eta := SingletonSourceHistory.eta
  eta_injective := SingletonSourceHistory.eta_injective
  supportOfCode := data.supportOfCode
  support_code := data.support_code
  base := SingletonSourceHistory.base
  support_singleton := SingletonSourceHistory.support_singleton
  base_represented := SingletonSourceHistory.base_represented
  fixedPrefix_pos := SingletonSourceHistory.fixedPrefix_pos
  arithmetic := data.arithmetic
  cost_le := data.cost_le
  event_subset := fun _ hs ↦ hs

theorem measure_majorant_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {width externalThreshold : ℕ} {ratio : ℝ≥0∞}
    (hm : 1 < m) (hk : 0 < k)
    (data : PhysicalBroadStrongSingletonProductData t o m k supportAt
      supportData width externalThreshold ratio) :
    simpleRandomWalk (physicalBroadStrongSingletonMajorant t o m k supportAt
      supportData width externalThreshold) ≤ 3 * ratio :=
  data.toHistoryData.measure_event_le hm hk

end PhysicalBroadStrongSingletonProductData

/-- Premise-free high-slot singleton product once the eventual scale and
concrete capacity facts are available. -/
noncomputable def broadStrongSingletonProductDataOfScale
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point)
    (support_code : ∀ s n, supportAt s n = supportOfCode
      (fixedOrientedTypedExternalWordCode t o n s))
    (scale : CandidateLocalBroadThetaScaleArithmetic m)
    (capacity : HLOZCandidateLocalLazyCap.sourceCandidateLazyCap48 m +
      concreteExternalThreshold48 m + candidateLocalBroadWidth48 m ≤ m + 1) :
    PhysicalBroadStrongSingletonProductData t o m k supportAt supportData
      (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)
      (broadStrongSingletonRatio m) where
  supportOfCode := supportOfCode
  support_code := support_code
  arithmetic := fun history cap ↦ externalBroadSourceArithmetic_of_scale
    supportData history.eta cap scale capacity
  cost_le := fun history cap ↦ broadStrongSingleton_cost_le
    supportData history cap

noncomputable def broadStrongLowSingletonProductDataOfScale
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (slot : Fin (hlozCutoff44 m + 1))
    (scale : CandidateLocalBroadThetaScaleArithmetic m)
    (capacity : HLOZCandidateLocalLazyCap.sourceCandidateLazyCap48 m +
      concreteExternalThreshold48 m + candidateLocalBroadWidth48 m ≤ m + 1) :
    PhysicalBroadStrongSingletonProductData t o m k
      (lowFilteredSlotSupportAt t o m slot)
      (lowFilteredSlotSupportData t o m k slot)
      (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)
      (broadStrongLowSingletonRatio m) where
  supportOfCode := lowFilteredSlotSupportOfCode t o m slot
  support_code := fun _ _ ↦ rfl
  arithmetic := fun history cap ↦ externalBroadSourceArithmetic_of_scale
    (lowFilteredSlotSupportData t o m k slot) history.eta cap scale capacity
  cost_le := fun history cap ↦ broadStrongLowSingleton_cost_le history cap

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongSingletonProduct
