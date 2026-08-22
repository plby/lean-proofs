/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongSingletonProduct
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaPositiveSlotProduct
import ErdosProblems.Erdos1165.TilingOrientedVisitedBaseExternalSupport

/-!
# Positive-prefix products for broad strong source slots

High retained-count bases are indexed by the Proposition 4.4 candidate
budget.  Low bases are indexed by physical creation-time slots, with the
low test built into the support selector.  Each slot is reconstructed into
the honest actual-endpoint-increment product.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongPositiveSlotProduct

open ExternalProposition44 HLOZGapEstimate HLOZPathEvents
open HLOZCandidateLocalBroadSourceStrongRoute
open HLOZCandidateLocalBroadThetaProduct
open HLOZCandidateLocalBroadThetaStrongSingletonProduct
open HLOZConcreteFullBetaProductData
open HLOZShellZeroReplacementWindows
open HLOZSourceOrientedExternalLocalTime
open HLOZSourceOrientedThetaCreationSlots
open HLOZSourceOrientedThetaLowSlotSupport
open HLOZSourceOrientedThetaPositiveSlotProduct
open HLOZSourceOrientedThetaSingletonHistoryProduct
open HLOZSourceOrientedThetaSlotSupport
open LazyDecomposition SpatialInsertionFiber TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedRetainedSourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingOrientedVisitedBaseExternalSupport
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Physical strong singleton event before choosing its complete external
creation code. -/
def physicalPositiveSingletonBroadStrongEvent
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (width externalThreshold : ℕ) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    ∃ b, supportAt s (creationTimeNat m k s) = {b} ∧
      (let z := fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k s) s;
        0 < z.initial.1.length + 2 * z.retainedCount + z.tail.1.length) ∧
      b ∈ orientedBroadSourceLowThetaStrongBases t o m width
        externalThreshold s (creationTimeNat m k s)}

theorem physicalPositiveSingletonBroadStrongEvent_subset_majorant
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (width externalThreshold : ℕ) :
    physicalPositiveSingletonBroadStrongEvent t o m k supportAt width
        externalThreshold ⊆
      physicalBroadStrongSingletonMajorant t o m k supportAt supportData
        width externalThreshold := by
  classical
  intro s hs
  rcases hs with ⟨hvalid, hreach, b, hsupport, hfixedPos, hbstrong⟩
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
    rw [orientedBroadSourceLowThetaStrongBases, Finset.mem_filter] at hbstrong
    rw [HLOZCandidateLocalBroadSourceLowThetaGeometry.orientedBroadSourceLowThetaBases,
      Finset.mem_filter] at hbstrong
    exact hbstrong.1.2.1
  let history : SingletonSourceHistory t o m k supportAt :=
    ⟨eta, b, rfl, hbrepresented, hcompat, by
      simpa only [eta, z] using hfixedPos⟩
  have hcomplete :=
    (concreteFiber o m k supportAt supportData eta).atom_complete hatom
  rcases Set.mem_iUnion.mp hcomplete with ⟨cap, hcap⟩
  apply Set.mem_iUnion.mpr
  refine ⟨history, Set.mem_iUnion.mpr ⟨cap, ?_⟩⟩
  exact ⟨by simpa only
      [HLOZSourceOrientedThetaSourceSlotCapCover.sourceSlotAtomCap,
        history, eta] using hcap, hbstrong⟩

/-- High physical broad-source slot. -/
def broadStrongCreationHighSlotBad (t : DominoTiling) (o : Orientation)
    (m k width externalThreshold : ℕ) (slot : Fin (hlozSiteBudget44 m)) :
    Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    creationTimeNat m k s ≤ hlozCutoff44 m ∧
    ∃ b, finsetSlot (orientedThetaCreationCandidateSites44 t o m k s) slot =
        some b ∧
      b ∈ orientedBroadSourceLowThetaStrongBases t o m width
        externalThreshold s (creationTimeNat m k s)}

/-- Low physical broad-source slot. -/
def broadStrongCreationLowSlotBad (t : DominoTiling) (o : Orientation)
    (m k width externalThreshold : ℕ)
    (slot : Fin (hlozCutoff44 m + 1)) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    creationTimeNat m k s ≤ hlozCutoff44 m ∧
    ∃ b, finsetSlot (orientedThetaCreationBases t o m k s) slot = some b ∧
      tilingSourceExternalBaseLocalTime t o s (creationTimeNat m k s) b <
        hlozThickLevel44 m ∧
      b ∈ orientedBroadSourceLowThetaStrongBases t o m width
        externalThreshold s (creationTimeNat m k s)}

def positiveBroadStrongHighSlotBad (t : DominoTiling) (o : Orientation)
    (m k width externalThreshold : ℕ) (slot : Fin (hlozSiteBudget44 m)) :
    Set WalkPath :=
  broadStrongCreationHighSlotBad t o m k width externalThreshold slot ∩
    positiveExternalCreationPrefix t o m k

def positiveBroadStrongLowSlotBad (t : DominoTiling) (o : Orientation)
    (m k width externalThreshold : ℕ)
    (slot : Fin (hlozCutoff44 m + 1)) : Set WalkPath :=
  broadStrongCreationLowSlotBad t o m k width externalThreshold slot ∩
    positiveExternalCreationPrefix t o m k

private theorem lowFilteredSlotSupportAt_creation_eq_singleton_of_count
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {slot : Fin (hlozCutoff44 m + 1)} {s : WalkPath} {b : Point}
    (hvalid : s ∈ (validStepWalk : Set WalkPath))
    (hcreation : 0 < creationTimeNat m k s)
    (hslot : finsetSlot (orientedThetaCreationBases t o m k s) slot = some b)
    (hlow : tilingSourceExternalBaseLocalTime t o s
      (creationTimeNat m k s) b < hlozThickLevel44 m) :
    lowFilteredSlotSupportAt t o m slot s (creationTimeNat m k s) = {b} := by
  classical
  have hbcode := finsetSlot_eq_some_mem hslot
  have hrepresented := (mem_orientedThetaCodeBases_iff.mp hbcode).1
  have hcompat := (mem_orientedThetaCodeBases_iff.mp hbcode).2
  have hcard :=
    card_tilingCoordinatesAt_fixedOrientedTypedExternalWordCode_eq_source
      t o s (creationTimeNat m k s) hvalid hcreation
        ⟨b, hrepresented⟩ hcompat
  have hlowCode : HLOZSourceOrientedThetaCreationSlots.orientedThetaCodeExternalCount
      t (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s) b <
        hlozThickLevel44 m := by
    simpa [HLOZSourceOrientedThetaCreationSlots.orientedThetaCodeExternalCount,
      hrepresented, hcard] using hlow
  unfold lowFilteredSlotSupportAt lowFilteredSlotSupportOfCode
  unfold orientedThetaCreationBases at hslot
  simp [hslot, hlowCode]

theorem positiveBroadStrongHighSlotBad_subset_majorant
    (t : DominoTiling) (o : Orientation)
    (m k width externalThreshold : ℕ) (slot : Fin (hlozSiteBudget44 m)) :
    positiveBroadStrongHighSlotBad t o m k width externalThreshold slot ⊆
      physicalBroadStrongSingletonMajorant t o m k
        (highSlotSupportAt t o m slot) (highSlotSupportData t o m k slot)
        width externalThreshold := by
  intro s hs
  rcases hs with
    ⟨⟨hvalid, hreach, _hclock, b, hslot, hbstrong⟩, hpositive⟩
  apply physicalPositiveSingletonBroadStrongEvent_subset_majorant
    (highSlotSupportData t o m k slot) width externalThreshold
  exact ⟨hvalid, hreach, b, highSlotSupportAt_creation_eq_singleton hslot,
    hpositive, hbstrong⟩

theorem positiveBroadStrongLowSlotBad_subset_majorant
    (t : DominoTiling) (o : Orientation)
    (m k width externalThreshold : ℕ)
    (slot : Fin (hlozCutoff44 m + 1)) (hm : 1 < m) (hk : 0 < k) :
    positiveBroadStrongLowSlotBad t o m k width externalThreshold slot ⊆
      physicalBroadStrongSingletonMajorant t o m k
        (lowFilteredSlotSupportAt t o m slot)
        (lowFilteredSlotSupportData t o m k slot) width externalThreshold := by
  intro s hs
  rcases hs with
    ⟨⟨hvalid, hreach, _hclock, b, hslot, hlow, hbstrong⟩, hpositive⟩
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
  apply physicalPositiveSingletonBroadStrongEvent_subset_majorant
    (lowFilteredSlotSupportData t o m k slot) width externalThreshold
  exact ⟨hvalid, hreach, b,
    lowFilteredSlotSupportAt_creation_eq_singleton_of_count hvalid hcreation
      hslot hlow,
    hpositive, hbstrong⟩

def positiveBroadStrongHighProductMajorant
    (t : DominoTiling) (o : Orientation) (m k width externalThreshold : ℕ) :
    Set WalkPath :=
  ⋃ slot : Fin (hlozSiteBudget44 m),
    physicalBroadStrongSingletonMajorant t o m k
      (highSlotSupportAt t o m slot) (highSlotSupportData t o m k slot)
      width externalThreshold

def positiveBroadStrongLowProductMajorant
    (t : DominoTiling) (o : Orientation) (m k width externalThreshold : ℕ) :
    Set WalkPath :=
  ⋃ slot : Fin (hlozCutoff44 m + 1),
    physicalBroadStrongSingletonMajorant t o m k
      (lowFilteredSlotSupportAt t o m slot)
      (lowFilteredSlotSupportData t o m k slot) width externalThreshold

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

theorem simpleRandomWalk_positiveBroadStrongHighProductMajorant_le
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (scale : CandidateLocalBroadThetaScaleArithmetic m)
    (capacity : HLOZCandidateLocalLazyCap.sourceCandidateLazyCap48 m +
      concreteExternalThreshold48 m + candidateLocalBroadWidth48 m ≤ m + 1) :
    simpleRandomWalk (positiveBroadStrongHighProductMajorant t o m k
      (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)) ≤
      (hlozSiteBudget44 m : ℝ≥0∞) * (3 * broadStrongSingletonRatio m) := by
  let event := fun slot : Fin (hlozSiteBudget44 m) ↦
    physicalBroadStrongSingletonMajorant t o m k
      (highSlotSupportAt t o m slot) (highSlotSupportData t o m k slot)
      (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)
  have h : ∀ slot, simpleRandomWalk (event slot) ≤
      3 * broadStrongSingletonRatio m := by
    intro slot
    exact (broadStrongSingletonProductDataOfScale
      (highSlotSupportData t o m k slot)
      (highSlotSupportOfCode t o m slot) (fun _ _ ↦ rfl)
      scale capacity).measure_majorant_le hm hk
  simpa only [positiveBroadStrongHighProductMajorant, event, Fintype.card_fin]
    using measure_iUnion_le_card_mul event (3 * broadStrongSingletonRatio m) h

theorem simpleRandomWalk_positiveBroadStrongLowProductMajorant_le
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (scale : CandidateLocalBroadThetaScaleArithmetic m)
    (capacity : HLOZCandidateLocalLazyCap.sourceCandidateLazyCap48 m +
      concreteExternalThreshold48 m + candidateLocalBroadWidth48 m ≤ m + 1) :
    simpleRandomWalk (positiveBroadStrongLowProductMajorant t o m k
      (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)) ≤
      ((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
        (3 * broadStrongLowSingletonRatio m) := by
  let event := fun slot : Fin (hlozCutoff44 m + 1) ↦
    physicalBroadStrongSingletonMajorant t o m k
      (lowFilteredSlotSupportAt t o m slot)
      (lowFilteredSlotSupportData t o m k slot)
      (candidateLocalBroadWidth48 m) (concreteExternalThreshold48 m)
  have h : ∀ slot, simpleRandomWalk (event slot) ≤
      3 * broadStrongLowSingletonRatio m := by
    intro slot
    exact (broadStrongLowSingletonProductDataOfScale (t := t) (o := o)
      (k := k) slot scale capacity).measure_majorant_le hm hk
  simpa only [positiveBroadStrongLowProductMajorant, event, Fintype.card_fin]
    using measure_iUnion_le_card_mul event
      (3 * broadStrongLowSingletonRatio m) h

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongPositiveSlotProduct
