/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaLowSlotSupport
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSingletonScaleProduct

/-!
# Low-external singleton source product

The filtered low selector makes the unique exposed coordinate genuinely
low-external.  Consequently its stopped product pays only the stronger
`m^(1/2)` deviation cost; no high-external term is replicated over the
physical-time slot family.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaLowSingletonProduct

open ExternalProposition44 HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaCreationSlots
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaLowSlotSupport
open HLOZSourceOrientedThetaProduct
open HLOZSourceOrientedThetaSingletonHistoryProduct
open HLOZSourceOrientedThetaSingletonScaleProduct
open HLOZSourceOrientedThetaSourceSelectedCarrier
open LazyDecomposition TilingCappedMarginalization
open ScreeningInstantiation
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def lowSingletonSourceThetaRatio (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.exp (-17 * thetaLowRateScale m))

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
  have hb : history.base ∈
      supportAt s (creationTimeNat m k s) := by
    rw [hs.2.2.2, history.support_singleton]
    simp
  rw [support_code, hs.2.2.1] at hb
  exact hb

private theorem low_history_highCoordinates_eq_empty
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {slot : Fin (hlozCutoff44 m + 1)}
    (history : SingletonSourceHistory t o m k
      (lowFilteredSlotSupportAt t o m slot)) (cap : ℕ) :
    externalThetaHighCoordinates
      (withExternalSourceSelected
        (concreteFiber o m k (lowFilteredSlotSupportAt t o m slot)
          (lowFilteredSlotSupportData t o m k slot) history.eta)
        (HLOZProposition48Candidates.shellWidth48 m)
        (HLOZShellZeroExternalWindow.shellZeroExternalLow48 m)
        (HLOZShellZeroExternalWindow.shellZeroExternalHigh48 m)) cap = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  rw [externalThetaHighCoordinates, Finset.mem_filter] at hc
  have hcS := (away_mem_support_iff t history.eta.1.1.start
    history.eta.1.1.retained history.eta.1.2 c.1).1 c.2
  have hcS' : c.1.1 ∈ ({history.base} : Finset Point) := by
    simpa only [← history.support_singleton] using hcS
  have hcPoint : c.1.1 = history.base := by
    simpa only [Finset.mem_singleton] using hcS'
  have hbaseLow := externalCount_lt_of_mem_lowFilteredSlotSupportOfCode
    (history_base_mem_supportOfCode
      (lowFilteredSlotSupportOfCode t o m slot) (fun _ _ ↦ rfl) history)
  have hrepresented : history.base ∈ tilingExternalDominoBases t
      history.eta.1.1.start history.eta.1.1.retained :=
    history.base_represented
  have hbaseLow' : Fintype.card (TilingCoordinatesAt t
      history.eta.1.1.start history.eta.1.1.retained
      ⟨history.base, hrepresented⟩) < hlozThickLevel44 m := by
    simpa [orientedThetaCodeExternalCount, hrepresented] using hbaseLow
  have heq : c.1 = ⟨history.base, hrepresented⟩ := by
    apply Subtype.ext
    exact hcPoint
  rw [heq] at hc
  omega

theorem lowExternalSourceSelected_cost_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {slot : Fin (hlozCutoff44 m + 1)}
    (history : SingletonSourceHistory t o m k
      (lowFilteredSlotSupportAt t o m slot)) (cap : ℕ) :
    ENNReal.ofReal (2 * ∑ c, externalThetaCost
      (withExternalSourceSelected
        (concreteFiber o m k (lowFilteredSlotSupportAt t o m slot)
          (lowFilteredSlotSupportData t o m k slot) history.eta)
        (HLOZProposition48Candidates.shellWidth48 m)
        (HLOZShellZeroExternalWindow.shellZeroExternalLow48 m)
        (HLOZShellZeroExternalWindow.shellZeroExternalHigh48 m)) cap c) ≤
      lowSingletonSourceThetaRatio m := by
  let sourceData := withExternalSourceSelected
    (concreteFiber o m k (lowFilteredSlotSupportAt t o m slot)
      (lowFilteredSlotSupportData t o m k slot) history.eta)
      (HLOZProposition48Candidates.shellWidth48 m)
      (HLOZShellZeroExternalWindow.shellZeroExternalLow48 m)
      (HLOZShellZeroExternalWindow.shellZeroExternalHigh48 m)
  have hsum := sum_externalThetaCost_le sourceData cap
  have hzero := low_history_highCoordinates_eq_empty history cap
  have hreal : 2 * ∑ c, externalThetaCost sourceData cap c ≤
      2 * Real.exp (-17 * thetaLowRateScale m) := by
    calc
      2 * ∑ c, externalThetaCost sourceData cap c ≤
          2 * (((externalThetaHighCoordinates sourceData cap).card : ℝ) *
              Real.exp (-17 * balanceRateScale m) +
            (history.eta.1.2.card : ℝ) *
              Real.exp (-17 * thetaLowRateScale m)) := by
        gcongr
      _ = 2 * Real.exp (-17 * thetaLowRateScale m) := by
        rw [hzero, history.support_singleton]
        simp
  exact ENNReal.ofReal_le_ofReal hreal

/-- Literal low-external singleton product, with the high contribution
eliminated by the retained-code selector. -/
noncomputable def lowSingletonSourceThetaProductData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (slot : Fin (hlozCutoff44 m + 1))
    (scale : OrientedThetaScaleArithmetic m) :
    SingletonSourceThetaProductData t o m k
      (lowFilteredSlotSupportAt t o m slot)
      (lowFilteredSlotSupportData t o m k slot)
      (HLOZProposition48Candidates.shellWidth48 m)
      (HLOZShellZeroExternalWindow.shellZeroExternalLow48 m)
      (HLOZShellZeroExternalWindow.shellZeroExternalHigh48 m)
      (lowSingletonSourceThetaRatio m) where
  supportOfCode := lowFilteredSlotSupportOfCode t o m slot
  support_code := fun _ _ ↦ rfl
  arithmetic := fun history cap ↦
    externalSourceSelectedArithmetic_of_scale
      (lowFilteredSlotSupportData t o m k slot) history.eta cap scale
  cost_le := fun history cap ↦
    lowExternalSourceSelected_cost_le history cap

theorem simpleRandomWalk_lowSingletonSourceThetaProductMajorant_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (slot : Fin (hlozCutoff44 m + 1))
    (hm : 1 < m) (hk : 0 < k) (scale : OrientedThetaScaleArithmetic m) :
    simpleRandomWalk
      (singletonSourceThetaProductMajorant t o m k
        (lowFilteredSlotSupportAt t o m slot)
        (lowFilteredSlotSupportData t o m k slot)
        (HLOZProposition48Candidates.shellWidth48 m)
        (HLOZShellZeroExternalWindow.shellZeroExternalLow48 m)
        (HLOZShellZeroExternalWindow.shellZeroExternalHigh48 m)) ≤
      3 * lowSingletonSourceThetaRatio m :=
  (lowSingletonSourceThetaProductData slot scale).measure_majorant_le hm hk

end

end Erdos1165.HLOZSourceOrientedThetaLowSingletonProduct
