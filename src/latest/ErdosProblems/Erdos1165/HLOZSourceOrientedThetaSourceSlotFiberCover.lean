/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceSingletonAccepted
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSlotSupport
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaWindowSplit
import ErdosProblems.Erdos1165.HLOZTypedStoppedCandidateObservability

/-!
# Physical source-Theta slots enter the accepted stopped product

This is the path-space seam for the rank-stable `I₁` half of the restricted
oriented Theta screen.  A retained-word slot fixes a singleton support.  The
cofinal external creation fibre then supplies a capped coordinate vector for
the physical path.  Prefix invariance transports the physical `V₂` and
source-window facts to its canonical reconstruction, where the singleton
accepted-creation theorem applies.

The above-level replacement window is deliberately absent.  It requires the
separate actual-endpoint-increment replacement partition.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSourceOrientedThetaSourceSlotFiberCover

open FiniteDominoProductLaw HLOZPathEvents HLOZProposition48Candidates
open ExternalProposition44 HLOZGapEstimate
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaCreationSlots
open HLOZSourceOrientedThetaExternalSourceAccepted
open HLOZSourceOrientedThetaSlotSupport
open HLOZSourceOrientedThetaSourceSelectedCarrier
open HLOZSourceOrientedThetaSourceSingletonAccepted
open HLOZSourceOrientedThetaWindowSplit
open HLOZTypedStoppedCandidateObservability
open HLOZThetaSourceBalance
open HLOZShellZeroReplacementWindows
open LazyDecomposition PathInsertion PreStoppingFiber SpatialInsertionFiber
open StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedRetainedSourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open TilingDistinguishedTraceInvariant TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The capped accepted source-Theta stopped fibres over every nonempty
external-code/singleton-support atom. -/
def externalSourceThetaScreenedFiberUnion
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (w externalLow externalHigh : ℕ) : Set WalkPath :=
  ⋃ eta : SupportedIndex t o m k supportAt, ⋃ cap : ℕ,
    let data := concreteFiber o m k supportAt supportData eta
    let sourceData := withExternalSourceSelected data w externalLow externalHigh
    walkLift (prefixedTilingPreStoppingFiberEvent
      (sourceData.stoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
      eta.1.1.retained (sourceData.coordinateCap cap) eta.1.1.tail.1
      (externalAcceptedSourceThetaPredicate sourceData w externalLow
        externalHigh cap))

theorem measurableSet_externalSourceThetaScreenedFiberUnion
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (w externalLow externalHigh : ℕ) :
    MeasurableSet (externalSourceThetaScreenedFiberUnion t o m k supportAt
      supportData w externalLow externalHigh) := by
  apply MeasurableSet.iUnion
  intro eta
  apply MeasurableSet.iUnion
  intro cap
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    ((withExternalSourceSelected
      (concreteFiber o m k supportAt supportData eta)
        w externalLow externalHigh).isStoppingTime cap)
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    ((withExternalSourceSelected
      (concreteFiber o m k supportAt supportData eta)
        w externalLow externalHigh).coordinateCap cap)
    eta.1.1.tail.1
    (externalAcceptedSourceThetaPredicate
      (withExternalSourceSelected
        (concreteFiber o m k supportAt supportData eta)
          w externalLow externalHigh)
      w externalLow externalHigh cap)

/-- Generic singleton-slot reconstruction.  This theorem is independent of
whether the slot came from the high Proposition 4.4 family or from the low
creation-word family. -/
theorem mem_externalSourceThetaScreenedFiberUnion_of_singleton
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point)
    (support_code : ∀ s n, supportAt s n = supportOfCode
      (fixedOrientedTypedExternalWordCode t o n s))
    (hm : 1 < m) (hk : 0 < k) (w externalLow externalHigh : ℕ)
    {s : WalkPath} {b : Point}
    (hvalid : s ∈ (validStepWalk : Set WalkPath))
    (hreach : ReachesThreshold s m k)
    (hsupport : supportAt s (creationTimeNat m k s) = {b})
    (hbsource : b ∈ orientedRestrictedThetaSourceAtCreation
      t o m k w externalLow externalHigh s) :
    s ∈ externalSourceThetaScreenedFiberUnion t o m k supportAt supportData
      w externalLow externalHigh := by
  classical
  let z := fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s
  let S : Finset Point := {b}
  have hatom : s ∈ orientedExternalAllCreationSupportTraceAtom
      t o m k supportAt z S := by
    rw [orientedExternalAllCreationSupportTraceAtom_eq]
    exact ⟨hvalid, hreach, rfl, hsupport⟩
  let eta : SupportedIndex t o m k supportAt := ⟨(z, S), ⟨s, hatom⟩⟩
  let data := concreteFiber o m k supportAt supportData eta
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  have hcomplete := data.atom_complete hatom
  rcases Set.mem_iUnion.mp hcomplete with ⟨cap, hcap⟩
  rcases hcap with ⟨hvalid', hpre⟩
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
  have hcreationS : ThresholdCreation s m k (creationTimeNat m k s) := by
    simpa only [creationTimeNat, hreach, dif_pos] using
      thresholdCreation_natFind hreach
  have htime : creationTimeNat m k s = v.length := by
    have hstop := q.2.2
    change truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
        (extendPrefix (directionVectorOfList v)) = v.length at hstop
    have hlt : v.length <
        externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
      let dummy : TilingCreationFavoriteData := ((∅, ∅),
        (eta.1.1.start, eta.1.1.start))
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
  have hbtheta :=
    (Finset.mem_filter.mp hbsource).1
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
      rw [hsupport]
      simp
    simpa only [eta, z] using
      supportData.represented s (creationTimeNat m k s) hvalid hmem
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
    rw [← htime]
    rw [← localTime_eq_of_pathPrefix_eq hpTime b]
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
    have hcard :=
      card_tilingCoordinatesAt_fixedOrientedTypedExternalWordCode_eq_source
        t o s (creationTimeNat m k s) hvalid hcreationPos
          ⟨b, by simpa only [eta, z] using hbrepresented⟩ hcompat
    simpa only [eta, z, hcard] using hbtheta.2
  have hpredicate : externalAcceptedSourceThetaPredicate sourceData w
      externalLow externalHigh cap q.1 := by
    exact externalAcceptedSourceThetaPredicate_of_singleton_source
      supportData supportOfCode support_code eta hm hk cap w externalLow
      externalHigh b rfl hbrepresented hcompat q.1
      q.2.2
      (shellZeroSourceTotalWindow m w ∪ shellZeroReplacementTotalWindow m w)
      (by simpa only [sq, v] using hbVTwoQ)
      (by simpa only [sq, v] using hbsourceQ) hexternal
  apply Set.mem_iUnion.mpr
  refine ⟨eta, Set.mem_iUnion.mpr ⟨cap, ?_⟩⟩
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

/-! ## The source-window slot family -/

/-- A high retained-word slot whose selected restricted-Theta base lies in
the rank-stable source window. -/
def orientedThetaCreationHighSourceSlotBad (t : DominoTiling)
    (o : Orientation) (m k w externalLow externalHigh : ℕ)
    (slot : Fin (ExternalProposition44.hlozSiteBudget44 m)) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    creationTimeNat m k s ≤ ExternalProposition44.hlozCutoff44 m ∧
    ∃ b, finsetSlot
        (orientedThetaCreationCandidateSites44 t o m k s) slot = some b ∧
      b ∈ orientedRestrictedThetaHighAtCreation t o m k w externalLow
        externalHigh s ∧
      b ∈ orientedRestrictedThetaSourceAtCreation t o m k w externalLow
        externalHigh s}

/-- A low retained-word slot whose selected restricted-Theta base lies in
the rank-stable source window. -/
def orientedThetaCreationLowSourceSlotBad (t : DominoTiling)
    (o : Orientation) (m k w externalLow externalHigh : ℕ)
    (slot : Fin (ExternalProposition44.hlozCutoff44 m + 1)) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    creationTimeNat m k s ≤ ExternalProposition44.hlozCutoff44 m ∧
    ∃ b, finsetSlot (orientedThetaCreationBases t o m k s) slot = some b ∧
      b ∈ orientedRestrictedThetaLowAtCreation t o m k w externalLow
        externalHigh s ∧
      b ∈ orientedRestrictedThetaSourceAtCreation t o m k w externalLow
        externalHigh s}

def someOrientedThetaCreationHighSourceSlotBad (t : DominoTiling)
    (o : Orientation) (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (Finset.univ : Finset
      (Fin (ExternalProposition44.hlozSiteBudget44 m)))
    (orientedThetaCreationHighSourceSlotBad t o m k w externalLow externalHigh)

def someOrientedThetaCreationLowSourceSlotBad (t : DominoTiling)
    (o : Orientation) (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (Finset.univ : Finset (Fin (ExternalProposition44.hlozCutoff44 m + 1)))
    (orientedThetaCreationLowSourceSlotBad t o m k w externalLow externalHigh)

/-- The exact retained-slot payment for the source-window half. -/
def orientedRestrictedThetaSourceCreationPaidEvent (t : DominoTiling)
    (o : Orientation) (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  validStepWalkᶜ ∪
    (orientedThetaCandidateOverflow44 t o m ∪
      (someOrientedThetaCreationHighSourceSlotBad t o m k w externalLow
          externalHigh ∪
        someOrientedThetaCreationLowSourceSlotBad t o m k w externalLow
          externalHigh))

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

theorem highSourceSlotBad_subset_screenedFiberUnion
    (t : DominoTiling) (o : Orientation) (m k w externalLow externalHigh : ℕ)
    (slot : Fin (ExternalProposition44.hlozSiteBudget44 m))
    (hm : 1 < m) (hk : 0 < k) :
    orientedThetaCreationHighSourceSlotBad t o m k w externalLow externalHigh
        slot ⊆
      externalSourceThetaScreenedFiberUnion t o m k
        (highSlotSupportAt t o m slot) (highSlotSupportData t o m k slot)
        w externalLow externalHigh := by
  intro s hs
  rcases hs with ⟨hvalid, hreach, _hclock, b, hslot, _hhigh, hbsource⟩
  apply mem_externalSourceThetaScreenedFiberUnion_of_singleton
    (highSlotSupportData t o m k slot) (highSlotSupportOfCode t o m slot)
    (fun _ _ ↦ rfl) hm hk w externalLow externalHigh hvalid hreach
      (highSlotSupportAt_creation_eq_singleton hslot) hbsource

theorem lowSourceSlotBad_subset_screenedFiberUnion
    (t : DominoTiling) (o : Orientation) (m k w externalLow externalHigh : ℕ)
    (slot : Fin (ExternalProposition44.hlozCutoff44 m + 1))
    (hm : 1 < m) (hk : 0 < k) :
    orientedThetaCreationLowSourceSlotBad t o m k w externalLow externalHigh
        slot ⊆
      externalSourceThetaScreenedFiberUnion t o m k
        (lowSlotSupportAt t o m slot) (lowSlotSupportData t o m k slot)
        w externalLow externalHigh := by
  intro s hs
  rcases hs with ⟨hvalid, hreach, _hclock, b, hslot, _hlow, hbsource⟩
  apply mem_externalSourceThetaScreenedFiberUnion_of_singleton
    (lowSlotSupportData t o m k slot) (lowSlotSupportOfCode t o m slot)
    (fun _ _ ↦ rfl) hm hk w externalLow externalHigh hvalid hreach
      (lowSlotSupportAt_creation_eq_singleton hslot) hbsource

/-- Union of the high-slot accepted stopped products. -/
def someHighSourceScreenedFiberUnion (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  ⋃ slot : Fin (ExternalProposition44.hlozSiteBudget44 m),
    externalSourceThetaScreenedFiberUnion t o m k
      (highSlotSupportAt t o m slot) (highSlotSupportData t o m k slot)
      w externalLow externalHigh

/-- Union of the low-slot accepted stopped products. -/
def someLowSourceScreenedFiberUnion (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  ⋃ slot : Fin (ExternalProposition44.hlozCutoff44 m + 1),
    externalSourceThetaScreenedFiberUnion t o m k
      (lowSlotSupportAt t o m slot) (lowSlotSupportData t o m k slot)
      w externalLow externalHigh

theorem measurableSet_someHighSourceScreenedFiberUnion
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) :
    MeasurableSet (someHighSourceScreenedFiberUnion t o m k w externalLow
      externalHigh) := by
  apply MeasurableSet.iUnion
  intro slot
  exact measurableSet_externalSourceThetaScreenedFiberUnion t o m k
    (highSlotSupportAt t o m slot) (highSlotSupportData t o m k slot)
    w externalLow externalHigh

theorem measurableSet_someLowSourceScreenedFiberUnion
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) :
    MeasurableSet (someLowSourceScreenedFiberUnion t o m k w externalLow
      externalHigh) := by
  apply MeasurableSet.iUnion
  intro slot
  exact measurableSet_externalSourceThetaScreenedFiberUnion t o m k
    (lowSlotSupportAt t o m slot) (lowSlotSupportData t o m k slot)
    w externalLow externalHigh

/-- Product-facing majorant.  Only the already-paid Proposition 4.4 overflow
and invalid-walk complement remain outside the literal stopped products. -/
def orientedRestrictedThetaSourceProductMajorant (t : DominoTiling)
    (o : Orientation) (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  validStepWalkᶜ ∪
    (orientedThetaCandidateOverflow44 t o m ∪
      (someHighSourceScreenedFiberUnion t o m k w externalLow externalHigh ∪
        someLowSourceScreenedFiberUnion t o m k w externalLow externalHigh))

theorem sourceCreationPaid_subset_productMajorant
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ)
    (hm : 1 < m) (hk : 0 < k) :
    orientedRestrictedThetaSourceCreationPaidEvent t o m k w externalLow
        externalHigh ⊆
      orientedRestrictedThetaSourceProductMajorant t o m k w externalLow
        externalHigh := by
  intro s hs
  rcases hs with hinvalid | hoverflow | hslot
  · left; exact hinvalid
  · right; left; exact hoverflow
  · rcases hslot with hhigh | hlow
    · right; right; left
      rcases hhigh with ⟨slot, _hslot, hs⟩
      exact Set.mem_iUnion.mpr
        ⟨slot, highSourceSlotBad_subset_screenedFiberUnion
          t o m k w externalLow externalHigh slot hm hk hs⟩
    · right; right; right
      rcases hlow with ⟨slot, _hslot, hs⟩
      exact Set.mem_iUnion.mpr
        ⟨slot, lowSourceSlotBad_subset_screenedFiberUnion
          t o m k w externalLow externalHigh slot hm hk hs⟩

/-- Physical on-time source-window restricted Theta is covered by the
Prop. 4.4 overflow and the two exact retained-word slot families. -/
theorem restrictedThetaSource_onTime_subset_creationPaid
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ)
    (hm : 1 < m) (hk : 0 < k) :
    {s | ReachesThreshold s m k ∧
      creationTimeNat m k s ≤ ExternalProposition44.hlozCutoff44 m ∧
      (orientedRestrictedThetaSourceAtCreation t o m k w externalLow
        externalHigh s).Nonempty} ⊆
      orientedRestrictedThetaSourceCreationPaidEvent t o m k w externalLow
        externalHigh := by
  intro s hs
  rcases hs with ⟨hreach, hclock, b, hbsource⟩
  by_cases hvalid : s ∈ validStepWalk
  · have hbtheta := (Finset.mem_filter.mp hbsource).1
    have hsplit : b ∈ orientedRestrictedThetaHighAtCreation t o m k w
          externalLow externalHigh s ∨
        b ∈ orientedRestrictedThetaLowAtCreation t o m k w externalLow
          externalHigh s := by
      rw [← Finset.mem_union,
        ← orientedTilingThetaAtCreation_eq_high_union_low]
      exact hbtheta
    rcases hsplit with hhigh | hlow
    · by_cases hoverflow : s ∈ orientedThetaCandidateOverflow44 t o m
      · right; left; exact hoverflow
      · right; right; left
        have hcreation := creationTimeNat_pos_of_reaches hm hk hreach
        have hbcand :=
          orientedRestrictedThetaHighAtCreation_subset_creationCandidates44
            hm hk hvalid hreach hhigh
        obtain ⟨j, hjlt, hj⟩ := exists_finsetSlot_eq_some hbcand
        have hjbudget : j < ExternalProposition44.hlozSiteBudget44 m :=
          hjlt.trans_le (orientedThetaCreationCandidateSites44_card_le
            hvalid hcreation hclock hoverflow)
        exact ⟨⟨j, hjbudget⟩, Finset.mem_univ _, hvalid, hreach, hclock,
          b, by simpa using hj, hhigh, hbsource⟩
    · right; right; right
      have hbbase :=
        orientedRestrictedThetaLowAtCreation_subset_creationBases hvalid hlow
      obtain ⟨j, hjlt, hj⟩ := exists_finsetSlot_eq_some hbbase
      have hjcut : j < ExternalProposition44.hlozCutoff44 m + 1 :=
        hjlt.trans_le (orientedThetaCreationBases_card_le_cutoff_add_one hclock)
      exact ⟨⟨j, hjcut⟩, Finset.mem_univ _, hvalid, hreach, hclock,
        b, by simpa using hj, hlow, hbsource⟩
  · left; exact hvalid

end

end Erdos1165.HLOZSourceOrientedThetaSourceSlotFiberCover
