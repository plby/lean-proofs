/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedShellSupportSelector
import ErdosProblems.Erdos1165.TilingShellZeroSourcePrefixInvariant

/-!
# Concrete cap coverage of one exact static-support shell source

The source cap predicate is the literal canonical exact-source predicate.
Prefix invariance turns it into a sound stopped cylinder.  Cofinal coverage
and cap monotonicity are inherited from the already constructed physical
external-word/support family rather than postulated.
-/

open Set

namespace Erdos1165.TilingShellZeroSourceCapCoverage

open HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroReplacementWindows LazyDecomposition
open PathInsertion PreStoppingFiber SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization
open TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellSupportSelector
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroAllCreationTraceBridge
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroSourcePrefixInvariant
open TilingShellZeroSourceScreenForward
open TilingShellZeroSourcePartition VariableStoppedTracePartition
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Forget the shell conditions while retaining the same physical external
word and source support. -/
noncomputable def sourceExternalSupportedIndex
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) :
    TilingOrientedExternalAllCreationStoppedCoordinate.SupportedIndex
      t o m k (orientedShellZeroSourceSupportAt t o m) := by
  refine ⟨eta.1, ?_⟩
  rcases eta.2 with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [orientedExternalAllCreationSupportTraceAtom_eq]
  rcases hs with ⟨⟨⟨hevent, hcode⟩, hvalid⟩, hsupport⟩
  change fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s =
    eta.1.1 at hcode
  change sourceStaticSupport t o m k (shellWidth48 m) s = eta.1.2 at hsupport
  exact ⟨hvalid, hevent.1, hcode, by
    simpa only [sourceStaticSupport, orientedShellZeroSourceSupportAt]
      using hsupport⟩

/-- The pre-existing concrete cofinal carrier underlying a supported source
static-support atom. -/
noncomputable def sourceCarrier
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) :=
  concreteFiber o m k (orientedShellZeroSourceSupportAt t o m)
    (orientedShellZeroSourceSupportSelectorData t o m k)
    (sourceExternalSupportedIndex eta)

@[simp] theorem sourceCarrier_coordinateCap
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) (cap : ℕ) :
    (sourceCarrier eta).coordinateCap cap = coordinateCap eta.1.1 m cap := rfl

@[simp] theorem sourceCarrier_stoppingTime
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) (cap : ℕ) :
    (sourceCarrier eta).stoppingTime cap = sourceStoppingTime eta.1.1 m k cap :=
  rfl

/-- A literal exact-source predicate refines the generic external-word
predicate on the same capped coordinates. -/
theorem externalStoppedAtomPredicate_of_source
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total cap : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      (coordinateCap eta.1.1 m cap))
    (hsource : sourcePredicate t o m k low externalLow externalHigh total cap
      eta.1.1 eta.1.2 q)
    (haccepted : PrefixedTilingStoppingAccepted
      (sourceStoppingTime eta.1.1 m k cap) eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
          eta.1.1.tail.1) :
    externalStoppedAtomPredicate o m k
      (orientedShellZeroSourceSupportAt t o m) eta.1.2 eta.1.1
        (coordinateCap eta.1.1 m cap) q := by
  let canonical := canonicalPath eta.1.1 (fun j ↦ (q j : ℕ))
  let favorite := (fixedOrientedAllCreationTraceCode t o
    (creationTimeNat m k canonical) canonical).favorite
  refine ⟨favorite, ?_⟩
  intro omega homega
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
  let somega := trajectory omega
  have hp : pathPrefix canonical v.length = pathPrefix somega v.length := by
    simpa only [canonical, somega, v, canonicalPath] using
      (pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
        eta.1.1.initial.1 eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 omega homega).symm
  have htime : creationTimeNat m k canonical = v.length := by
    simpa only [canonical, v] using source_creation_time_eq eta.1.1 q haccepted
  have hsourceOmega : somega ∈
      orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total
          eta.1.1 eta.1.2 := by
    apply exactSourceStaticSupportAtom_of_pathPrefix_eq hsource
      (trajectory_mem_validStepWalk omega)
    rw [htime]
    exact hp
  rcases hsourceOmega with
    ⟨⟨⟨hevent, _hcode⟩, hvalid⟩, hsupport⟩
  refine ⟨⟨hvalid, hevent.1, ?_⟩, ?_⟩
  · have htimeOmega : creationTimeNat m k somega = v.length := by
      have hcreation : ThresholdCreation canonical m k v.length := by
        apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
          m k (externalCoordinateCutoff eta.1.1
            (coordinateCap eta.1.1 m cap)) v.length
            (extendPrefix (directionVectorOfList v))
            (insertion_lt_cutoff eta.1.1 m cap q)).mp
        simpa only [PrefixedTilingStoppingAccepted, sourceStoppingTime,
          canonical, v] using haccepted
      exact creationTimeNat_eq_of_creation
        ((thresholdCreation_iff_of_pathPrefix_eq hp le_rfl).mp hcreation)
    rw [htimeOmega]
    calc
      fixedOrientedAllCreationTraceCode t o v.length somega =
          fixedOrientedAllCreationTraceCode t o v.length canonical :=
        (fixedOrientedAllCreationTraceCode_eq_of_pathPrefix_eq t o hp).symm
      _ = withFavorite eta.1.1 favorite := by
        rw [OrientedAllCreationTraceCode.mk.injEq]
        rcases hsource with ⟨⟨⟨_hevent, hcode⟩, _hvalid⟩, _hsupport⟩
        change fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k canonical) canonical = eta.1.1 at hcode
        rw [htime] at hcode
        refine ⟨hcode, ?_⟩
        simp only [favorite, htime, withFavorite]
  · change orientedShellZeroSourceSupportAt t o m somega
      (creationTimeNat m k somega) = eta.1.2
    change sourceStaticSupport t o m k (shellWidth48 m) somega = eta.1.2
      at hsupport
    simpa only [orientedShellZeroSourceSupportAt, sourceStaticSupport] using hsupport

/-- Every literal source cap cylinder is contained in its exact source
static-support atom. -/
theorem source_cap_sound
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) (cap : ℕ) :
    walkLift (prefixedTilingPreStoppingFiberEvent
      (sourceStoppingTime eta.1.1 m k cap) eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (coordinateCap eta.1.1 m cap)
      eta.1.1.tail.1 (sourcePredicate t o m k low externalLow externalHigh
        total cap eta.1.1 eta.1.2)) ⊆
      orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total
          eta.1.1 eta.1.2 := by
  intro s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1
  let canonical := canonicalPath eta.1.1 (fun j ↦ (q.1 j : ℕ))
  have hpRaw := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
    eta.1.1.initial.1 eta.1.1.start eta.1.1.retained
      (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1 (stepsOfWalk s) hq
  have hp : pathPrefix canonical v.length = pathPrefix s v.length := by
    have hp' : pathPrefix (trajectory (stepsOfWalk s)) v.length =
        pathPrefix canonical v.length := by
      simpa only [v, canonical, canonicalPath] using hpRaw
    rw [hvalid] at hp'
    exact hp'.symm
  have htime : creationTimeNat m k canonical = v.length := by
    simpa only [canonical, v] using source_creation_time_eq eta.1.1 q.1 q.2.2
  apply exactSourceStaticSupportAtom_of_pathPrefix_eq q.2.1 hvalid
  rw [htime]
  exact hp

/-- Forgetting the exact shell screen maps a literal source cap cylinder
into the concrete external-word/support cap cylinder with the same index. -/
theorem source_cap_subset_carrier_cap
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) (cap : ℕ) :
    walkLift (prefixedTilingPreStoppingFiberEvent
      (sourceStoppingTime eta.1.1 m k cap) eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (coordinateCap eta.1.1 m cap)
      eta.1.1.tail.1 (sourcePredicate t o m k low externalLow externalHigh
        total cap eta.1.1 eta.1.2)) ⊆
    walkLift (prefixedTilingPreStoppingFiberEvent
      ((sourceCarrier eta).stoppingTime cap) eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained ((sourceCarrier eta).coordinateCap cap)
      eta.1.1.tail.1 ((sourceCarrier eta).atomPredicate cap)) := by
  intro s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let qNat : Fin (eta.1.1.retainedCount + 1) → ℕ := fun j ↦ (q.1 j : ℕ)
  have hpred := externalStoppedAtomPredicate_of_source eta q.1 q.2.1 q.2.2
  let q' : TilingCappedCoordinates eta.1.1.retainedCount
      ((sourceCarrier eta).coordinateCap cap) := q.1
  have hpred' : (sourceCarrier eta).atomPredicate cap q' := by
    change externalStoppedAtomPredicate o m k
      (orientedShellZeroSourceSupportAt t o m) eta.1.2 eta.1.1
        ((sourceCarrier eta).coordinateCap cap) q'
    rcases hpred with ⟨favorite, hfull⟩
    refine ⟨favorite, ?_⟩
    intro omega homega
    apply hfull
    unfold prefixedTilingStoppedInsertionAtom at homega ⊢
    change truncatedLevelTime m k (externalCoordinateCutoff eta.1.1
        ((sourceCarrier eta).coordinateCap cap)) omega =
        (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1).length ∧
      incrementPrefixList
        (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1).length omega =
        prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1 at homega
    change truncatedLevelTime m k (externalCoordinateCutoff eta.1.1
        (coordinateCap eta.1.1 m cap)) omega =
        (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1).length ∧
      incrementPrefixList
        (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1).length omega =
        prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1
    have hcapEq := sourceCarrier_coordinateCap eta cap
    rw [hcapEq] at homega
    exact homega
  have haccepted' : PrefixedTilingStoppingAccepted
      ((sourceCarrier eta).stoppingTime cap) eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q' j : ℕ))
        eta.1.1.tail.1 := by
    unfold PrefixedTilingStoppingAccepted
    have htauEq := sourceCarrier_stoppingTime eta cap
    change (sourceCarrier eta).stoppingTime cap
      (extendPrefix (directionVectorOfList
        (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1))) =
      (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
        eta.1.1.retained qNat eta.1.1.tail.1).length
    rw [htauEq]
    simpa only [qNat, PrefixedTilingStoppingAccepted] using q.2.2
  have hstopped' : stepsOfWalk s ∈ prefixedTilingStoppedInsertionAtom
      ((sourceCarrier eta).stoppingTime cap) eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q' j : ℕ))
        eta.1.1.tail.1 := by
    unfold prefixedTilingStoppedInsertionAtom at hq ⊢
    have htauEq := sourceCarrier_stoppingTime eta cap
    change sourceStoppingTime eta.1.1 m k cap (stepsOfWalk s) =
        (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1).length ∧
      incrementPrefixList
        (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1).length (stepsOfWalk s) =
        prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1 at hq
    change (sourceCarrier eta).stoppingTime cap (stepsOfWalk s) =
        (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1).length ∧
      incrementPrefixList
        (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1).length (stepsOfWalk s) =
        prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained qNat eta.1.1.tail.1
    rw [htauEq]
    exact hq
  exact ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q', hpred', haccepted'⟩, hstopped'⟩⟩

/-- On a path already known to be in the exact source atom, membership in
one generic carrier cap reconstructs membership in the literal cap at the
same stage. -/
theorem source_cap_of_carrier_cap
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total cap : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) {s : WalkPath}
    (hs : s ∈ orientedValidShellZeroExactSourceStaticSupportAtom t o m k
      (shellWidth48 m) low externalLow externalHigh total eta.1.1 eta.1.2)
    (hcap : s ∈ walkLift (prefixedTilingPreStoppingFiberEvent
      ((sourceCarrier eta).stoppingTime cap) eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained ((sourceCarrier eta).coordinateCap cap)
      eta.1.1.tail.1 ((sourceCarrier eta).atomPredicate cap))) :
    s ∈ walkLift (prefixedTilingPreStoppingFiberEvent
      (sourceStoppingTime eta.1.1 m k cap) eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (coordinateCap eta.1.1 m cap)
      eta.1.1.tail.1 (sourcePredicate t o m k low externalLow externalHigh
        total cap eta.1.1 eta.1.2)) := by
  rcases hcap with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let qNat : Fin (eta.1.1.retainedCount + 1) → ℕ := fun j ↦ (q.1 j : ℕ)
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained qNat eta.1.1.tail.1
  let canonical := canonicalPath eta.1.1 qNat
  have hpRaw := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
    eta.1.1.initial.1 eta.1.1.start eta.1.1.retained qNat
      eta.1.1.tail.1 (stepsOfWalk s) hq
  have hp : pathPrefix s v.length = pathPrefix canonical v.length := by
    have hp' : pathPrefix (trajectory (stepsOfWalk s)) v.length =
        pathPrefix canonical v.length := by
      simpa only [v, canonical, canonicalPath] using hpRaw
    rw [hvalid] at hp'
    exact hp'
  have haccepted : PrefixedTilingStoppingAccepted
      (sourceStoppingTime eta.1.1 m k cap) eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained qNat eta.1.1.tail.1 := by
    have h : PrefixedTilingStoppingAccepted
        ((sourceCarrier eta).stoppingTime cap) eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained qNat eta.1.1.tail.1 := by
      simpa only [qNat, sourceExternalSupportedIndex] using q.2.2
    exact (sourceCarrier_stoppingTime eta cap) ▸ h
  have hcanonicalTime : creationTimeNat m k canonical = v.length := by
    simpa only [canonical, v] using source_creation_time_eq eta.1.1 q.1 q.2.2
  have hcanonicalCreation : ThresholdCreation canonical m k v.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (externalCoordinateCutoff eta.1.1
        (coordinateCap eta.1.1 m cap)) v.length
        (extendPrefix (directionVectorOfList v))
        (insertion_lt_cutoff eta.1.1 m cap q.1)).mp
    simpa only [PrefixedTilingStoppingAccepted, canonical, v,
      sourceStoppingTime] using haccepted
  have hsCreation : ThresholdCreation s m k v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp le_rfl).mpr hcanonicalCreation
  have hsTime : creationTimeNat m k s = v.length :=
    creationTimeNat_eq_of_creation hsCreation
  have hsource : canonical ∈
      orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total
          eta.1.1 eta.1.2 := by
    apply exactSourceStaticSupportAtom_of_pathPrefix_eq hs
      (trajectory_mem_validStepWalk _)
    rw [hsTime]
    exact hp
  refine ⟨hvalid, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact ⟨q.1, hsource, by simpa only [qNat] using haccepted⟩
  · exact hq

/-- Every path in the exact source atom occurs in one literal source cap
cylinder.  The cofinal cap is supplied by the concrete external-word fibre;
the stronger shell predicate is recovered from prefix invariance. -/
theorem source_complete
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) :
    orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total eta.1.1 eta.1.2 ⊆
      ⋃ cap, walkLift (prefixedTilingPreStoppingFiberEvent
        (sourceStoppingTime eta.1.1 m k cap) eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (coordinateCap eta.1.1 m cap)
        eta.1.1.tail.1 (sourcePredicate t o m k low externalLow externalHigh
          total cap eta.1.1 eta.1.2)) := by
  intro s hs
  have hext : s ∈ orientedExternalAllCreationSupportTraceAtom
      t o m k (orientedShellZeroSourceSupportAt t o m) eta.1.1 eta.1.2 := by
    rw [orientedExternalAllCreationSupportTraceAtom_eq]
    rcases hs with ⟨⟨⟨hevent, hcode⟩, hvalid⟩, hsupport⟩
    change fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s =
      eta.1.1 at hcode
    change sourceStaticSupport t o m k (shellWidth48 m) s = eta.1.2 at hsupport
    exact ⟨hvalid, hevent.1, hcode, by
      simpa only [sourceStaticSupport, orientedShellZeroSourceSupportAt]
        using hsupport⟩
  have hcomplete := (sourceCarrier eta).atom_complete hext
  rcases Set.mem_iUnion.mp hcomplete with ⟨cap, hcap⟩
  rcases hcap with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let qNat : Fin (eta.1.1.retainedCount + 1) → ℕ := fun j ↦ (q.1 j : ℕ)
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained qNat eta.1.1.tail.1
  let canonical := canonicalPath eta.1.1 qNat
  have hpRaw := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
    eta.1.1.initial.1 eta.1.1.start eta.1.1.retained
      qNat eta.1.1.tail.1 (stepsOfWalk s) hq
  have hp : pathPrefix s v.length = pathPrefix canonical v.length := by
    have hp' : pathPrefix (trajectory (stepsOfWalk s)) v.length =
        pathPrefix canonical v.length := by
      simpa only [v, canonical, canonicalPath] using hpRaw
    rw [hvalid] at hp'
    exact hp'
  have hcanonicalTime : creationTimeNat m k canonical = v.length := by
    simpa only [canonical, v] using source_creation_time_eq eta.1.1 q.1 q.2.2
  have haccepted : PrefixedTilingStoppingAccepted
      (sourceStoppingTime eta.1.1 m k cap) eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained qNat
        eta.1.1.tail.1 := by
    have h : PrefixedTilingStoppingAccepted
        ((sourceCarrier eta).stoppingTime cap) eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained qNat eta.1.1.tail.1 := by
      simpa only [qNat, sourceExternalSupportedIndex] using q.2.2
    exact (sourceCarrier_stoppingTime eta cap) ▸ h
  have hcanonicalCreation : ThresholdCreation canonical m k v.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (externalCoordinateCutoff eta.1.1
        (coordinateCap eta.1.1 m cap)) v.length
        (extendPrefix (directionVectorOfList v))
        (insertion_lt_cutoff eta.1.1 m cap q.1)).mp
    simpa only [PrefixedTilingStoppingAccepted, canonical, v,
      sourceStoppingTime] using haccepted
  have hsCreation : ThresholdCreation s m k v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp le_rfl).mpr hcanonicalCreation
  have hsTime : creationTimeNat m k s = v.length :=
    creationTimeNat_eq_of_creation hsCreation
  have hsource : canonical ∈
      orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total
          eta.1.1 eta.1.2 := by
    apply exactSourceStaticSupportAtom_of_pathPrefix_eq hs
      (trajectory_mem_validStepWalk _)
    rw [hsTime]
    exact hp
  apply Set.mem_iUnion.mpr
  refine ⟨cap, ⟨hvalid, ?_⟩⟩
  apply Set.mem_iUnion.mpr
  refine ⟨⟨q.1, hsource, by simpa only [qNat] using haccepted⟩, ?_⟩
  exact hq

/-- The literal exact-source cap cylinders are monotone along the cofinal
cap schedule. -/
theorem source_monotone
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) :
    Monotone fun cap ↦ walkLift (prefixedTilingPreStoppingFiberEvent
      (sourceStoppingTime eta.1.1 m k cap) eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (coordinateCap eta.1.1 m cap)
      eta.1.1.tail.1 (sourcePredicate t o m k low externalLow externalHigh
        total cap eta.1.1 eta.1.2)) := by
  intro cap cap' hcap s hs
  have hsource := source_cap_sound eta cap hs
  have hcarrier := source_cap_subset_carrier_cap eta cap hs
  have hcarrier' := (sourceCarrier eta).atom_monotone hcap hcarrier
  exact source_cap_of_carrier_cap eta hsource hcarrier'

end

end Erdos1165.TilingShellZeroSourceCapCoverage
