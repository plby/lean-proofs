/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongPositiveSlotProduct

/-!
# On-time broad strong source cover

An on-time strong broad-source base is first represented in the retained
endpoint word.  Its oriented external count then gives the exact high/low
slot split.  Positive deleted prefixes enter the stopped products; the sole
zero-prefix branch is isolated for the fixed-origin estimate.
-/

open Set

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongCreationCover

open ExternalProposition44 HLOZGapEstimate HLOZPathEvents
open HLOZCandidateLocalBroadSourceStrongRoute
open HLOZCandidateLocalBroadThetaStrongPositiveSlotProduct
open HLOZSourceOrientedExternalLocalTime
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaCreationSlots
open HLOZSourceOrientedThetaPositiveSlotProduct
open HLOZSourceOrientedThetaSlotSupport
open LazyDecomposition SpatialInsertionFiber TilingLazyDecomposition
open TilingOrientedShellZeroSourcePartition
open TilingOrientedVisitedBaseExternalSupport
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def positiveBroadStrongSourceProductMajorant
    (t : DominoTiling) (o : Orientation) (m k width externalThreshold : ℕ) :
    Set WalkPath :=
  validStepWalkᶜ ∪
    (orientedThetaCandidateOverflow44 t o m ∪
      (positiveBroadStrongHighProductMajorant t o m k width externalThreshold ∪
        positiveBroadStrongLowProductMajorant t o m k width externalThreshold))

def zeroPrefixBroadStrongSourceEvent
    (t : DominoTiling) (o : Orientation) (m k width externalThreshold : ℕ) :
    Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    creationTimeNat m k s ≤ hlozCutoff44 m ∧
    (orientedBroadSourceLowThetaStrongBases t o m width externalThreshold s
      (creationTimeNat m k s)).Nonempty ∧
    s ∉ positiveExternalCreationPrefix t o m k}

private theorem creationTimeNat_pos_of_reaches
    {m k : ℕ} {s : WalkPath} (hm : 1 < m) (hk : 0 < k)
    (hreach : ReachesThreshold s m k) :
    0 < creationTimeNat m k s := by
  have hcreation : ThresholdCreation s m k (creationTimeNat m k s) := by
    simpa only [creationTimeNat, hreach, dif_pos] using
      thresholdCreation_natFind hreach
  by_contra hn
  have hzero : creationTimeNat m k s = 0 := Nat.eq_zero_of_not_pos hn
  have hsite := position_mem_thresholdSites_of_creation hk hcreation
  have hlevel := (mem_thresholdSites s _ m _).mp hsite |>.2
  have hlocal : localTime s 0 (s 0) = 1 := by
    simp [localTime, localTimePrefix, pathPrefix]
  rw [hzero, hlocal] at hlevel
  omega

private theorem strongBase_mem_creationBases
    {t : DominoTiling} {o : Orientation} {m k width externalThreshold : ℕ}
    {s : WalkPath} {b : Point}
    (hvalid : s ∈ (validStepWalk : Set WalkPath))
    (hcreation : 0 < creationTimeNat m k s)
    (hb : b ∈ orientedBroadSourceLowThetaStrongBases t o m width
      externalThreshold s (creationTimeNat m k s)) :
    b ∈ orientedThetaCreationBases t o m k s := by
  classical
  rw [orientedBroadSourceLowThetaStrongBases, Finset.mem_filter] at hb
  have hblower := hb.1
  rw [HLOZCandidateLocalBroadSourceLowThetaGeometry.orientedBroadSourceLowThetaBases,
    Finset.mem_filter] at hblower
  rcases hblower with ⟨hvisited, hcompat, hwindow, _hexternal⟩
  have hbase : tilingBase t b = b := by
    rw [visitedTilingBases, Finset.mem_image] at hvisited
    obtain ⟨x, _hx, hxbase⟩ := hvisited
    rw [← hxbase]
    exact tilingBase_idem t x
  have hpositive : 0 < localTime s (creationTimeNat m k s) b := by
    simp only [HLOZShellZeroReplacementWindows.mem_shellZeroSourceTotalWindow]
      at hwindow
    omega
  have hrepresented := tilingBase_mem_fixedExternalDominoBases_of_positive
    t o s (creationTimeNat m k s) hvalid hcreation b hbase hcompat hpositive
  unfold orientedThetaCreationBases
  exact mem_orientedThetaCodeBases_iff.mpr ⟨hrepresented, hcompat⟩

/-- On-time physical strong source is paid by the positive high/low stopped
products, Proposition 4.4 overflow, or the literal zero-prefix event. -/
theorem broadStrongSource_onTime_subset_positive_or_zero
    (t : DominoTiling) (o : Orientation)
    (m k width externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) :
    {s | ReachesThreshold s m k ∧ creationTimeNat m k s ≤ hlozCutoff44 m ∧
      (orientedBroadSourceLowThetaStrongBases t o m width externalThreshold s
        (creationTimeNat m k s)).Nonempty} ⊆
      positiveBroadStrongSourceProductMajorant t o m k width
          externalThreshold ∪
        zeroPrefixBroadStrongSourceEvent t o m k width externalThreshold := by
  classical
  intro s hs
  rcases hs with ⟨hreach, hclock, b, hbstrong⟩
  by_cases hvalid : s ∈ validStepWalk
  · have hcreation := creationTimeNat_pos_of_reaches hm hk hreach
    have hbbase := strongBase_mem_creationBases hvalid hcreation hbstrong
    let sourceCount := tilingSourceExternalBaseLocalTime t o s
      (creationTimeNat m k s) b
    by_cases hhigh : hlozThickLevel44 m ≤ sourceCount
    · by_cases hoverflow : s ∈ orientedThetaCandidateOverflow44 t o m
      · left
        right; left
        exact hoverflow
      · have hbcand : b ∈ orientedThetaCreationCandidateSites44 t o m k s := by
          rw [mem_orientedThetaCreationCandidateSites44_iff hvalid hcreation]
          exact ⟨hbbase, hhigh⟩
        obtain ⟨j, hjlt, hj⟩ := exists_finsetSlot_eq_some hbcand
        have hjbudget : j < hlozSiteBudget44 m :=
          hjlt.trans_le (orientedThetaCreationCandidateSites44_card_le
            hvalid hcreation hclock hoverflow)
        let slot : Fin (hlozSiteBudget44 m) := ⟨j, hjbudget⟩
        have hbad : s ∈ broadStrongCreationHighSlotBad t o m k width
            externalThreshold slot :=
          ⟨hvalid, hreach, hclock, b, by simpa only [slot] using hj, hbstrong⟩
        by_cases hpositive : s ∈ positiveExternalCreationPrefix t o m k
        · left
          right; right; left
          apply Set.mem_iUnion.mpr
          refine ⟨slot, positiveBroadStrongHighSlotBad_subset_majorant
            t o m k width externalThreshold slot ?_⟩
          exact ⟨hbad, hpositive⟩
        · right
          exact ⟨hvalid, hreach, hclock, ⟨b, hbstrong⟩, hpositive⟩
    · have hlow : sourceCount < hlozThickLevel44 m := Nat.lt_of_not_ge hhigh
      obtain ⟨j, hjlt, hj⟩ := exists_finsetSlot_eq_some hbbase
      have hjcut : j < hlozCutoff44 m + 1 :=
        hjlt.trans_le (orientedThetaCreationBases_card_le_cutoff_add_one hclock)
      let slot : Fin (hlozCutoff44 m + 1) := ⟨j, hjcut⟩
      have hbad : s ∈ broadStrongCreationLowSlotBad t o m k width
          externalThreshold slot :=
        ⟨hvalid, hreach, hclock, b, by simpa only [slot] using hj,
          hlow, hbstrong⟩
      by_cases hpositive : s ∈ positiveExternalCreationPrefix t o m k
      · left
        right; right; right
        apply Set.mem_iUnion.mpr
        refine ⟨slot, positiveBroadStrongLowSlotBad_subset_majorant
          t o m k width externalThreshold slot hm hk ?_⟩
        exact ⟨hbad, hpositive⟩
      · right
        exact ⟨hvalid, hreach, hclock, ⟨b, hbstrong⟩, hpositive⟩
  · left
    left
    exact hvalid

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongCreationCover
