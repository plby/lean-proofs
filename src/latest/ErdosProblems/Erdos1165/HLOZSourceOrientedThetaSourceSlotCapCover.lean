/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaHistoryCap
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceSlotFiberCover

/-!
# Same-cap physical source-slot cover

The accepted source selector is not itself definitionally monotone in the
coordinate cap.  The monotone object is the physical source event intersected
with the underlying stopped creation atom.  This file proves that this
physical cap piece lies in the strengthened source-Theta product fibre at the
same cap.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSourceOrientedThetaSourceSlotCapCover

open HLOZPathEvents
open HLOZSourceOrientedThetaExternalSourceAccepted
open HLOZSourceOrientedExternalLocalTime
open HLOZSourceOrientedThetaSourceActualDeltaCapBound
open HLOZSourceOrientedThetaSourceSelectedCarrier
open HLOZSourceOrientedThetaSourceSingletonAccepted
open HLOZSourceOrientedThetaWindowSplit
open HLOZThetaSourceBalance
open HLOZShellZeroReplacementWindows
open HLOZTypedStoppedCandidateObservability
open LazyDecomposition PathInsertion PreStoppingFiber SpatialInsertionFiber
open StoppedInsertion
open TilingCappedMarginalization TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedRetainedSourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open TilingDistinguishedTraceInvariant
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The monotone underlying stopped creation atom at one coordinate cap. -/
def sourceSlotAtomCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt) (cap : ℕ) : Set WalkPath :=
  let data := concreteFiber o m k supportAt supportData eta
  walkLift (prefixedTilingPreStoppingFiberEvent
    (data.stoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
    eta.1.1.retained (data.coordinateCap cap) eta.1.1.tail.1
    (data.atomPredicate cap))

theorem sourceSlotAtomCap_monotone
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt) :
    Monotone (sourceSlotAtomCap supportData eta) := by
  exact (concreteFiber o m k supportAt supportData eta).atom_monotone

/-- The physical singleton source-Theta event inside one monotone atom cap. -/
def physicalSingletonSourceThetaCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt) (b : Point)
    (cap w externalLow externalHigh : ℕ) : Set WalkPath :=
  sourceSlotAtomCap supportData eta cap ∩
    {s | b ∈ orientedRestrictedThetaSourceAtCreation
      t o m k w externalLow externalHigh s}

theorem physicalSingletonSourceThetaCap_monotone
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt) (b : Point)
    (w externalLow externalHigh : ℕ) :
    Monotone fun cap ↦ physicalSingletonSourceThetaCap supportData eta b cap
      w externalLow externalHigh := by
  intro cap cap' hcap s hs
  exact ⟨sourceSlotAtomCap_monotone supportData eta hcap hs.1, hs.2⟩

theorem card_tilingCoordinatesAt_eq_source_of_fixedCode_eq
    {t : DominoTiling} {o : Orientation} {s : WalkPath} {n : ℕ}
    (hvalid : s ∈ (validStepWalk : Set WalkPath)) (hn : 0 < n)
    (z : OrientedTilingTypedExternalWordCode t)
    (hcode : fixedOrientedTypedExternalWordCode t o n s = z)
    (b : TilingExternalDomino t z.start z.retained)
    (hb : OrientationCompatible o b.1) :
    Fintype.card (TilingCoordinatesAt t z.start z.retained b) =
      tilingSourceExternalBaseLocalTime t o s n b.1 := by
  subst z
  exact card_tilingCoordinatesAt_fixedOrientedTypedExternalWordCode_eq_source
    t o s n hvalid hn b hb

theorem physicalSingletonSourceThetaCap_empty_or_vTwo
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt) (b : Point)
    (cap w externalLow externalHigh : ℕ) :
    physicalSingletonSourceThetaCap supportData eta b cap w externalLow
        externalHigh = ∅ ∨
      ∃ (q₀ : TilingCappedCoordinates eta.1.1.retainedCount
          ((concreteFiber o m k supportAt supportData eta).coordinateCap cap))
        (window : Finset ℕ),
        let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
          eta.1.1.start eta.1.1.retained (fun j ↦ (q₀ j : ℕ))
            eta.1.1.tail.1
        let sq := trajectory (extendPrefix (directionVectorOfList v))
        tilingVTwoAt t window sq v.length b := by
  classical
  by_cases hempty :
      physicalSingletonSourceThetaCap supportData eta b cap w externalLow
        externalHigh = ∅
  · exact Or.inl hempty
  · right
    obtain ⟨s, hcap, hbsource⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    rcases hcap with ⟨hvalid, hpre⟩
    rcases Set.mem_iUnion.mp hpre with ⟨q, hq⟩
    let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1
    let sq := trajectory (extendPrefix (directionVectorOfList v))
    have hp : pathPrefix s v.length = pathPrefix sq v.length := by
      have hp' := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
        eta.1.1.initial.1 eta.1.1.start eta.1.1.retained
        (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1 (stepsOfWalk s) hq
      change trajectory (stepsOfWalk s) = s at hvalid
      rw [hvalid] at hp'
      simpa only [v, sq] using hp'
    let data := concreteFiber o m k supportAt supportData eta
    have hstop := q.2.2
    change truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
        (extendPrefix (directionVectorOfList v)) = v.length at hstop
    have hlt : v.length <
        externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
      let dummy : TilingCreationFavoriteData :=
        ((∅, ∅), (eta.1.1.start, eta.1.1.start))
      have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
        (withFavorite eta.1.1 dummy) (data.coordinateCap cap) q.1
      rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
      exact hraw
    have hcreationQ : ThresholdCreation sq m k v.length :=
      (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
        m k (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
        v.length _ hlt).mp hstop
    have hcreationS : ThresholdCreation s m k v.length :=
      (thresholdCreation_iff_of_pathPrefix_eq hp
        (Nat.le_refl v.length)).mpr hcreationQ
    have htime : creationTimeNat m k s = v.length :=
      creationTimeNat_eq_of_creation hcreationS
    change b ∈ orientedRestrictedThetaSourceAtCreation
      t o m k w externalLow externalHigh s at hbsource
    have hbtheta := (Finset.mem_filter.mp hbsource).1
    rw [orientedTilingThetaAtCreation, orientedTilingThetaBases,
      Finset.mem_filter, mem_orientedTilingVTwoBases_iff] at hbtheta
    have hbVTwoS : tilingVTwoAt t
        (shellZeroSourceTotalWindow m w ∪ shellZeroReplacementTotalWindow m w)
        s v.length b := by
      rw [tilingVTwoBases, Finset.mem_filter] at hbtheta
      rw [← htime]
      exact hbtheta.1.1.2
    refine ⟨q.1,
      shellZeroSourceTotalWindow m w ∪ shellZeroReplacementTotalWindow m w,
      ?_⟩
    simpa only [v, sq] using
      (tilingVTwoAt_iff_of_pathPrefix_eq t _ hp b).mp hbVTwoS

/-- Same-cap reconstruction of a physical source-window singleton into the
strengthened accepted stopped product. -/
theorem physicalSingletonSourceThetaCap_subset_sourceThetaCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point)
    (support_code : ∀ s n, supportAt s n = supportOfCode
      (fixedOrientedTypedExternalWordCode t o n s))
    (eta : SupportedIndex t o m k supportAt)
    (b : Point) (hsingleton : eta.1.2 = {b})
    (hm : 1 < m) (hk : 0 < k) (cap w externalLow externalHigh : ℕ) :
    physicalSingletonSourceThetaCap supportData eta b cap w externalLow
        externalHigh ⊆
      sourceThetaCap supportData eta cap w externalLow externalHigh := by
  classical
  intro s hs
  rcases hs with ⟨hcap, hbsource⟩
  let data := concreteFiber o m k supportAt supportData eta
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  have hatom := data.atom_sound cap hcap
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hatom
  rcases hcap with ⟨hvalid', hpre⟩
  rcases Set.mem_iUnion.mp hpre with ⟨q, hq⟩
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  have hp : pathPrefix s v.length = pathPrefix sq v.length := by
    have hp' := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
      eta.1.1.initial.1 eta.1.1.start eta.1.1.retained
      (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1 (stepsOfWalk s) hq
    have hwalk : trajectory (stepsOfWalk s) = s := hatom.1
    rw [hwalk] at hp'
    simpa only [v, sq] using hp'
  have hcreationS : ThresholdCreation s m k (creationTimeNat m k s) := by
    simpa only [creationTimeNat, hatom.2.1, dif_pos] using
      thresholdCreation_natFind hatom.2.1
  have htime : creationTimeNat m k s = v.length := by
    have hstop := q.2.2
    change truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
        (extendPrefix (directionVectorOfList v)) = v.length at hstop
    have hlt : v.length <
        externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
      let dummy : TilingCreationFavoriteData :=
        ((∅, ∅), (eta.1.1.start, eta.1.1.start))
      have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
        (withFavorite eta.1.1 dummy) (data.coordinateCap cap) q.1
      rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
      exact hraw
    have hcreationQ : ThresholdCreation sq m k v.length :=
      (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
        m k (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
        v.length _ hlt).mp hstop
    exact creationTimeNat_eq_of_creation
      ((thresholdCreation_iff_of_pathPrefix_eq hp
        (Nat.le_refl v.length)).mpr hcreationQ)
  change b ∈ orientedRestrictedThetaSourceAtCreation
    t o m k w externalLow externalHigh s at hbsource
  have hbtheta := (Finset.mem_filter.mp hbsource).1
  have hbsourceWindow := (Finset.mem_filter.mp hbsource).2
  rw [orientedTilingThetaAtCreation, orientedTilingThetaBases,
    Finset.mem_filter, mem_orientedTilingVTwoBases_iff] at hbtheta
  have hbVTwoS : tilingVTwoAt t
      (shellZeroSourceTotalWindow m w ∪ shellZeroReplacementTotalWindow m w)
      s (creationTimeNat m k s) b := by
    rw [tilingVTwoBases, Finset.mem_filter] at hbtheta
    exact hbtheta.1.1.2
  have hcompat : OrientationCompatible o b := hbtheta.1.2
  have hbrepresented : b ∈
      tilingExternalDominoBases t eta.1.1.start eta.1.1.retained := by
    have hmem : b ∈ supportAt s (creationTimeNat m k s) := by
      rw [hatom.2.2.2, hsingleton]
      simp
    rw [← hatom.2.2.1]
    exact supportData.represented s (creationTimeNat m k s) hatom.1 hmem
  have hpTime : pathPrefix s (creationTimeNat m k s) =
      pathPrefix sq (creationTimeNat m k s) := by
    rw [htime]
    exact hp
  have hbVTwoQ : tilingVTwoAt t
      (shellZeroSourceTotalWindow m w ∪ shellZeroReplacementTotalWindow m w)
      sq v.length b := by
    rw [← htime]
    exact (tilingVTwoAt_iff_of_pathPrefix_eq t _ hpTime b).mp hbVTwoS
  have hbsourceQ : localTime sq v.length b ∈
      shellZeroSourceTotalWindow m w := by
    rw [← htime, ← localTime_eq_of_pathPrefix_eq hpTime b]
    exact hbsourceWindow
  have hexternal : ¬(externalLow ≤
        Fintype.card (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained
          ⟨b, hbrepresented⟩) ∧
      Fintype.card (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained
          ⟨b, hbrepresented⟩) < externalHigh) := by
    have hcreationPos : 0 < creationTimeNat m k s := by
      by_contra hn
      have hzero := Nat.eq_zero_of_not_pos hn
      have hsite := position_mem_thresholdSites_of_creation hk hcreationS
      have hlevel := (mem_thresholdSites s _ m _).mp hsite |>.2
      have hlocal : localTime s 0 (s 0) = 1 := by
        simp [localTime, localTimePrefix, pathPrefix]
      rw [hzero, hlocal] at hlevel
      omega
    have hcardEta := card_tilingCoordinatesAt_eq_source_of_fixedCode_eq
      hatom.1 hcreationPos eta.1.1 hatom.2.2.1
        ⟨b, hbrepresented⟩ hcompat
    simpa only [hcardEta] using hbtheta.2
  have hpredicate : externalAcceptedSourceThetaPredicate sourceData w
      externalLow externalHigh cap q.1 := by
    exact externalAcceptedSourceThetaPredicate_of_singleton_source
      supportData supportOfCode support_code eta hm hk cap w externalLow
      externalHigh b hsingleton hbrepresented hcompat q.1 q.2.2
      (shellZeroSourceTotalWindow m w ∪ shellZeroReplacementTotalWindow m w)
      (by simpa only [sq, v] using hbVTwoQ)
      (by simpa only [sq, v] using hbsourceQ) hexternal
  refine ⟨hvalid', ?_⟩
  let qsource : PrefixedTilingAcceptedCappedCoordinates
      (sourceData.stoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
      eta.1.1.retained (sourceData.coordinateCap cap) eta.1.1.tail.1
      (externalAcceptedSourceThetaPredicate sourceData w externalLow
        externalHigh cap) := ⟨q.1, hpredicate, q.2.2⟩
  apply Set.mem_iUnion.mpr
  refine ⟨qsource, ?_⟩
  simpa only [sourceData, withExternalSourceSelected_stoppingTime,
    withExternalSourceSelected_coordinateCap, qsource] using hq

end

end Erdos1165.HLOZSourceOrientedThetaSourceSlotCapCover
