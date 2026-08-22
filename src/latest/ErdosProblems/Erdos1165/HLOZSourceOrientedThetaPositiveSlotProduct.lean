/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaLowSingletonProduct
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceSlotFiberCover

/-!
# Positive-prefix source-Theta slot products

This module joins the physical high/low slot cover to the literal singleton
history products.  Histories whose deleted external word has positive fixed
prefix length enter those products directly.  The zero-prefix histories are
kept separate for the fixed-origin payment.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaPositiveSlotProduct

open ExternalProposition44 HLOZGapEstimate HLOZPathEvents
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaLowSingletonProduct
open HLOZSourceOrientedThetaLowSlotSupport
open HLOZSourceOrientedThetaProduct
open HLOZSourceOrientedThetaSingletonHistoryProduct
open HLOZSourceOrientedThetaSingletonScaleProduct
open HLOZSourceOrientedThetaSlotSupport
open HLOZSourceOrientedThetaSourceSlotFiberCover
open HLOZShellZeroExternalWindow HLOZProposition48Candidates
open LazyDecomposition
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The deleted external creation prefix has a genuine physical endpoint. -/
def positiveExternalCreationPrefix (t : DominoTiling) (o : Orientation)
    (m k : ℕ) : Set WalkPath :=
  fun s ↦
    let z := fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k s) s
    0 < z.initial.1.length + 2 * z.retainedCount + z.tail.1.length

def positiveHighSourceSlotBad (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ)
    (slot : Fin (hlozSiteBudget44 m)) : Set WalkPath :=
  orientedThetaCreationHighSourceSlotBad t o m k w externalLow externalHigh
      slot ∩
    positiveExternalCreationPrefix t o m k

def positiveLowSourceSlotBad (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ)
    (slot : Fin (hlozCutoff44 m + 1)) : Set WalkPath :=
  orientedThetaCreationLowSourceSlotBad t o m k w externalLow externalHigh
      slot ∩
    positiveExternalCreationPrefix t o m k

theorem positiveHighSourceSlotBad_subset_majorant
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ)
    (slot : Fin (hlozSiteBudget44 m)) :
    positiveHighSourceSlotBad t o m k w externalLow externalHigh slot ⊆
      singletonSourceThetaProductMajorant t o m k
        (highSlotSupportAt t o m slot) (highSlotSupportData t o m k slot)
        w externalLow externalHigh := by
  intro s hs
  rcases hs with
    ⟨⟨hvalid, hreach, _hclock, b, hslot, _hhigh, hbsource⟩, hpositive⟩
  change 0 <
    (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s).initial.1.length +
      2 * (fixedOrientedTypedExternalWordCode t o
        (creationTimeNat m k s) s).retainedCount +
      (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s).tail.1.length
    at hpositive
  apply physicalPositiveSingletonSourceThetaEvent_subset_majorant
    (highSlotSupportData t o m k slot) w externalLow externalHigh
  exact ⟨hvalid, hreach, b, highSlotSupportAt_creation_eq_singleton hslot,
    hpositive, hbsource⟩

theorem positiveLowSourceSlotBad_subset_majorant
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ)
    (slot : Fin (hlozCutoff44 m + 1))
    (hm : 1 < m) (hk : 0 < k) :
    positiveLowSourceSlotBad t o m k w externalLow externalHigh slot ⊆
      singletonSourceThetaProductMajorant t o m k
        (lowFilteredSlotSupportAt t o m slot)
        (lowFilteredSlotSupportData t o m k slot)
        w externalLow externalHigh := by
  intro s hs
  rcases hs with
    ⟨⟨hvalid, hreach, _hclock, b, hslot, hlow, hbsource⟩, hpositive⟩
  change 0 <
    (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s).initial.1.length +
      2 * (fixedOrientedTypedExternalWordCode t o
        (creationTimeNat m k s) s).retainedCount +
      (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s).tail.1.length
    at hpositive
  have hcreation : 0 < creationTimeNat m k s := by
    have hcreate : ThresholdCreation s m k (creationTimeNat m k s) := by
      simpa only [creationTimeNat, hreach, dif_pos] using
        thresholdCreation_natFind hreach
    by_contra hn
    have hzero : creationTimeNat m k s = 0 := Nat.eq_zero_of_not_pos hn
    have hsite := position_mem_thresholdSites_of_creation hk hcreate
    have hlevel := (mem_thresholdSites s _ m _).mp hsite |>.2
    have hlocal : localTime s 0 (s 0) = 1 := by
      simp [localTime, localTimePrefix, pathPrefix]
    rw [hzero, hlocal] at hlevel
    omega
  apply physicalPositiveSingletonSourceThetaEvent_subset_majorant
    (lowFilteredSlotSupportData t o m k slot) w externalLow externalHigh
  exact ⟨hvalid, hreach, b,
    lowFilteredSlotSupportAt_creation_eq_singleton hvalid hcreation hslot hlow,
    hpositive, hbsource⟩

/-- Product majorants for every positive high slot. -/
def positiveHighSourceProductMajorant (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  ⋃ slot : Fin (hlozSiteBudget44 m),
    singletonSourceThetaProductMajorant t o m k
      (highSlotSupportAt t o m slot) (highSlotSupportData t o m k slot)
      w externalLow externalHigh

/-- Product majorants for every positive low slot, with the low test built
into the support selector. -/
def positiveLowSourceProductMajorant (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  ⋃ slot : Fin (hlozCutoff44 m + 1),
    singletonSourceThetaProductMajorant t o m k
      (lowFilteredSlotSupportAt t o m slot)
      (lowFilteredSlotSupportData t o m k slot)
      w externalLow externalHigh

private theorem measure_iUnion_le_card_mul
    {ι : Type} [Fintype ι] (event : ι → Set WalkPath) (q : ℝ≥0∞)
    (h : ∀ i, simpleRandomWalk (event i) ≤ q) :
    simpleRandomWalk (⋃ i, event i) ≤ (Fintype.card ι : ℝ≥0∞) * q := by
  refine (measure_iUnion_fintype_le simpleRandomWalk event).trans ?_
  calc
    (∑ i, simpleRandomWalk (event i)) ≤ ∑ _i : ι, q := by
      apply Finset.sum_le_sum
      intro i _hi
      exact h i
    _ = (Fintype.card ι : ℝ≥0∞) * q := by simp

theorem simpleRandomWalk_positiveHighSourceProductMajorant_le
    (t : DominoTiling) (o : Orientation)
    (m k : ℕ)
    (hm : 1 < m) (hk : 0 < k) (scale : OrientedThetaScaleArithmetic m) :
    simpleRandomWalk (positiveHighSourceProductMajorant t o m k
      (shellWidth48 m) (shellZeroExternalLow48 m)
      (shellZeroExternalHigh48 m)) ≤
      (hlozSiteBudget44 m : ℝ≥0∞) *
        (3 * singletonSourceThetaRatio m) := by
  let event := fun slot : Fin (hlozSiteBudget44 m) ↦
    singletonSourceThetaProductMajorant t o m k
      (highSlotSupportAt t o m slot) (highSlotSupportData t o m k slot)
      (shellWidth48 m) (shellZeroExternalLow48 m)
      (shellZeroExternalHigh48 m)
  have h : ∀ slot, simpleRandomWalk (event slot) ≤
      3 * singletonSourceThetaRatio m := by
    intro slot
    exact simpleRandomWalk_singletonSourceThetaProductMajorant_le
      (highSlotSupportData t o m k slot)
      (highSlotSupportOfCode t o m slot) (fun _ _ ↦ rfl) hm hk scale
  simpa only [positiveHighSourceProductMajorant, event, Fintype.card_fin]
    using measure_iUnion_le_card_mul event (3 * singletonSourceThetaRatio m) h

theorem simpleRandomWalk_positiveLowSourceProductMajorant_le
    (t : DominoTiling) (o : Orientation)
    (m k : ℕ)
    (hm : 1 < m) (hk : 0 < k) (scale : OrientedThetaScaleArithmetic m) :
    simpleRandomWalk (positiveLowSourceProductMajorant t o m k
      (shellWidth48 m) (shellZeroExternalLow48 m)
      (shellZeroExternalHigh48 m)) ≤
      ((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
        (3 * lowSingletonSourceThetaRatio m) := by
  let event := fun slot : Fin (hlozCutoff44 m + 1) ↦
    singletonSourceThetaProductMajorant t o m k
      (lowFilteredSlotSupportAt t o m slot)
      (lowFilteredSlotSupportData t o m k slot)
      (shellWidth48 m) (shellZeroExternalLow48 m)
      (shellZeroExternalHigh48 m)
  have h : ∀ slot, simpleRandomWalk (event slot) ≤
      3 * lowSingletonSourceThetaRatio m := by
    intro slot
    exact simpleRandomWalk_lowSingletonSourceThetaProductMajorant_le
      slot hm hk scale
  simpa only [positiveLowSourceProductMajorant, event, Fintype.card_fin]
    using measure_iUnion_le_card_mul event (3 * lowSingletonSourceThetaRatio m) h

end

end Erdos1165.HLOZSourceOrientedThetaPositiveSlotProduct
