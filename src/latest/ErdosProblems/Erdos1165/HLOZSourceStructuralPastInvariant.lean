/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZNoLazyFilteredTransitions
import ErdosProblems.Erdos1165.HLOZNoLazyFilteredPastObservability
import ErdosProblems.Erdos1165.HLOZSourceCreationRecordInvariant

/-!
# Structural filtered pasts on canonical source fibres

The low-gap part of the first two filtered histories depends only on the
distinguished coordinates of a canonical source atom.  Candidate-overflow
payments are intentionally absent: they will be routed additively rather
than included in the conditional-product carrier.
-/

open Set

namespace Erdos1165.HLOZSourceStructuralPastInvariant

open HLOZNoLazyFilteredTransitions HLOZPathEvents
open HLOZNoLazyFilteredPastObservability HLOZSpatialAdapter
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZSourceCreationRecordInvariant
open LazyDecomposition PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber TilingDistinguishedTraceInvariant
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple

/-- First transition with only its structural low-gap failure removed. -/
def firstStructuralPast (t : DominoTiling) (m : ℕ)
    (a : GapTriple) : Set WalkPath :=
  firstTransitionEvent t m a \ firstLowGapFailureEvent t m a

/-- Second transition with both preceding structural low-gap failures
removed. -/
def secondStructuralPast (t : DominoTiling) (m : ℕ)
    (a : GapTriple) : Set WalkPath :=
  secondTransitionEvent t m a \
    (firstLowGapFailureEvent t m a ∪ secondLowGapFailureEvent t m a)

theorem measurableSet_firstStructuralPast
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (firstStructuralPast t m a) :=
  (measurableSet_firstTransitionEvent t m a).diff
    (measurableSet_firstLowGapFailureEvent t m a)

theorem measurableSet_secondStructuralPast
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (secondStructuralPast t m a) :=
  (measurableSet_secondTransitionEvent t m a).diff
    ((measurableSet_firstLowGapFailureEvent t m a).union
      (measurableSet_secondLowGapFailureEvent t m a))

private theorem mem_firstTransitionEvent_iff_creationTime
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (s : WalkPath) :
    s ∈ firstTransitionEvent t m a ↔
      s ∈ pairConfiguration t m a.1.1
        (creationTimeNat m 1 s) (creationTimeNat m 2 s) := by
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨n₁, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨n₂, hs⟩
    have h₁ : creationTimeNat m 1 s = n₁ :=
      creationTimeNat_eq_of_creation hs.1
    have h₂ : creationTimeNat m 2 s = n₂ :=
      creationTimeNat_eq_of_creation hs.2.1
    simpa only [h₁, h₂] using hs
  · intro hs
    exact Set.mem_iUnion_of_mem (creationTimeNat m 1 s) <|
      Set.mem_iUnion_of_mem (creationTimeNat m 2 s) hs

private theorem mem_firstLowGapFailureEvent_iff_creationTime
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (s : WalkPath) :
    s ∈ firstLowGapFailureEvent t m a ↔
      s ∈ pairConfiguration t m a.1.1
          (creationTimeNat m 1 s) (creationTimeNat m 2 s) ∩
        {u | lowGapDeficitFailure u m
          (creationTimeNat m 1 s) (creationTimeNat m 2 s)} := by
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨n₁, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨n₂, hs⟩
    have h₁ : creationTimeNat m 1 s = n₁ :=
      creationTimeNat_eq_of_creation hs.1.1
    have h₂ : creationTimeNat m 2 s = n₂ :=
      creationTimeNat_eq_of_creation hs.1.2.1
    simpa only [h₁, h₂] using hs
  · intro hs
    exact Set.mem_iUnion_of_mem (creationTimeNat m 1 s) <|
      Set.mem_iUnion_of_mem (creationTimeNat m 2 s) hs

private theorem mem_secondTransitionEvent_iff_creationTime
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (s : WalkPath) :
    s ∈ secondTransitionEvent t m a ↔
      s ∈ tripleConfiguration t m a.1.1 a.1.2
        (creationTimeNat m 1 s) (creationTimeNat m 2 s)
        (creationTimeNat m 3 s) := by
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨n₁, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨n₂, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨n₃, hs⟩
    have h₁ : creationTimeNat m 1 s = n₁ :=
      creationTimeNat_eq_of_creation hs.1
    have h₂ : creationTimeNat m 2 s = n₂ :=
      creationTimeNat_eq_of_creation hs.2.1
    have h₃ : creationTimeNat m 3 s = n₃ :=
      creationTimeNat_eq_of_creation hs.2.2.1
    simpa only [h₁, h₂, h₃] using hs
  · intro hs
    exact Set.mem_iUnion_of_mem (creationTimeNat m 1 s) <|
      Set.mem_iUnion_of_mem (creationTimeNat m 2 s) <|
        Set.mem_iUnion_of_mem (creationTimeNat m 3 s) hs

private theorem mem_secondLowGapFailureEvent_iff_creationTime
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (s : WalkPath) :
    s ∈ secondLowGapFailureEvent t m a ↔
      s ∈ tripleConfiguration t m a.1.1 a.1.2
          (creationTimeNat m 1 s) (creationTimeNat m 2 s)
          (creationTimeNat m 3 s) ∩
        {u | lowGapDeficitFailure u m
          (creationTimeNat m 2 s) (creationTimeNat m 3 s)} := by
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨n₁, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨n₂, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨n₃, hs⟩
    have h₁ : creationTimeNat m 1 s = n₁ :=
      creationTimeNat_eq_of_creation hs.1.1
    have h₂ : creationTimeNat m 2 s = n₂ :=
      creationTimeNat_eq_of_creation hs.1.2.1
    have h₃ : creationTimeNat m 3 s = n₃ :=
      creationTimeNat_eq_of_creation hs.1.2.2.1
    simpa only [h₁, h₂, h₃] using hs
  · intro hs
    exact Set.mem_iUnion_of_mem (creationTimeNat m 1 s) <|
      Set.mem_iUnion_of_mem (creationTimeNat m 2 s) <|
        Set.mem_iUnion_of_mem (creationTimeNat m 3 s) hs

/-- The structural first past is determined by the path prefix through the
rank-two creation clock. -/
theorem firstStructuralPast_iff_of_pathPrefix_eq_of_creation
    {s s' : WalkPath} {N m : ℕ} (t : DominoTiling) (a : GapTriple)
    (hp : pathPrefix s N = pathPrefix s' N)
    (hfinal : ThresholdCreation s m 2 N)
    (hfinal' : ThresholdCreation s' m 2 N) :
    s ∈ firstStructuralPast t m a ↔ s' ∈ firstStructuralPast t m a := by
  have htransition := firstTransitionEvent_iff_of_pathPrefix_eq_of_creation
    t a hp hfinal hfinal'
  by_cases hsTransition : s ∈ firstTransitionEvent t m a
  · have hsTransition' := htransition.mp hsTransition
    rcases Set.mem_iUnion.mp hsTransition with ⟨n₁, hsTransition⟩
    rcases Set.mem_iUnion.mp hsTransition with ⟨n₂, hpair⟩
    have hn₂ : n₂ = N := thresholdCreation_time_unique hpair.2.1 hfinal
    subst n₂
    have hn₁ : n₁ ≤ N :=
      (creation_time_lt (by omega) (by omega) (by omega) hpair.1 hfinal).le
    let z : PairCreationIndex := (n₁, N)
    have hsPair : s ∈ pairCreationAtom t m a z := hpair
    have hsPair' : s' ∈ pairCreationAtom t m a z :=
      (pairCreationAtom_iff_of_pathPrefix_eq t m a z hn₁ hp).mp hsPair
    have hbad : s ∈ firstLowGapFailureEvent t m a ↔
        s' ∈ firstLowGapFailureEvent t m a :=
      (mem_firstLowGapFailureEvent_iff_of_pairCreationAtom hsPair).trans <|
        (lowGapDeficitFailure_iff_of_pathPrefix_eq hp hn₁ le_rfl).trans <|
          (mem_firstLowGapFailureEvent_iff_of_pairCreationAtom hsPair').symm
    change
      (s ∈ firstTransitionEvent t m a ∧
          s ∉ firstLowGapFailureEvent t m a) ↔
        (s' ∈ firstTransitionEvent t m a ∧
          s' ∉ firstLowGapFailureEvent t m a)
    exact and_congr htransition (not_congr hbad)
  · have hsTransition' : s' ∉ firstTransitionEvent t m a := by
      rwa [← htransition]
    change
      (s ∈ firstTransitionEvent t m a ∧
          s ∉ firstLowGapFailureEvent t m a) ↔
        (s' ∈ firstTransitionEvent t m a ∧
          s' ∉ firstLowGapFailureEvent t m a)
    simp only [hsTransition, hsTransition', false_and]

/-- The structural second past is determined by the path prefix through the
rank-three creation clock. -/
theorem secondStructuralPast_iff_of_pathPrefix_eq_of_creation
    {s s' : WalkPath} {N m : ℕ} (t : DominoTiling) (a : GapTriple)
    (hp : pathPrefix s N = pathPrefix s' N)
    (hfinal : ThresholdCreation s m 3 N)
    (hfinal' : ThresholdCreation s' m 3 N) :
    s ∈ secondStructuralPast t m a ↔ s' ∈ secondStructuralPast t m a := by
  have htransition := secondTransitionEvent_iff_of_pathPrefix_eq_of_creation
    t a hp hfinal hfinal'
  by_cases hsTransition : s ∈ secondTransitionEvent t m a
  · have hsTransition' := htransition.mp hsTransition
    rcases Set.mem_iUnion.mp hsTransition with ⟨n₁, hsTransition⟩
    rcases Set.mem_iUnion.mp hsTransition with ⟨n₂, hsTransition⟩
    rcases Set.mem_iUnion.mp hsTransition with ⟨n₃, htriple⟩
    have hn₃ : n₃ = N := thresholdCreation_time_unique htriple.2.2.1 hfinal
    subst n₃
    have hn₁ : n₁ ≤ N :=
      (creation_time_lt (by omega) (by omega) (by omega) htriple.1 hfinal).le
    have hn₂ : n₂ ≤ N :=
      (creation_time_lt (by omega) (by omega) (by omega) htriple.2.1 hfinal).le
    let z : TripleCreationIndex := ((n₁, n₂), N)
    have hsTriple : s ∈ tripleCreationAtom t m a z := htriple
    have hsTriple' : s' ∈ tripleCreationAtom t m a z :=
      (tripleCreationAtom_iff_of_pathPrefix_eq t m a z hn₁ hn₂ hp).mp
        hsTriple
    have hbad₁ : s ∈ firstLowGapFailureEvent t m a ↔
        s' ∈ firstLowGapFailureEvent t m a :=
      (mem_firstLowGapFailureEvent_iff_of_tripleCreationAtom hsTriple).trans <|
        (lowGapDeficitFailure_iff_of_pathPrefix_eq hp hn₁ hn₂).trans <|
          (mem_firstLowGapFailureEvent_iff_of_tripleCreationAtom
            hsTriple').symm
    have hbad₂ : s ∈ secondLowGapFailureEvent t m a ↔
        s' ∈ secondLowGapFailureEvent t m a :=
      (mem_secondLowGapFailureEvent_iff_of_tripleCreationAtom hsTriple).trans <|
        (lowGapDeficitFailure_iff_of_pathPrefix_eq hp hn₂ le_rfl).trans <|
          (mem_secondLowGapFailureEvent_iff_of_tripleCreationAtom
            hsTriple').symm
    change
      (s ∈ secondTransitionEvent t m a ∧
          s ∉ firstLowGapFailureEvent t m a ∪
            secondLowGapFailureEvent t m a) ↔
        (s' ∈ secondTransitionEvent t m a ∧
          s' ∉ firstLowGapFailureEvent t m a ∪
            secondLowGapFailureEvent t m a)
    rw [Set.mem_union, Set.mem_union, htransition, hbad₁, hbad₂]
  · have hsTransition' : s' ∉ secondTransitionEvent t m a := by
      rwa [← htransition]
    change
      (s ∈ secondTransitionEvent t m a ∧
          s ∉ firstLowGapFailureEvent t m a ∪
            secondLowGapFailureEvent t m a) ↔
        (s' ∈ secondTransitionEvent t m a ∧
          s' ∉ firstLowGapFailureEvent t m a ∪
            secondLowGapFailureEvent t m a)
    simp only [hsTransition, hsTransition', false_and]

/-- On a rank-two canonical source atom, the structural first past is fixed
by the distinguished coordinate projection. -/
theorem sourceCanonical_firstStructuralPast_iff
    {t : DominoTiling} {o : Orientation} {m cap : ℕ}
    (eta : SourceSupportedIndex t o m 2) (hm : 1 < m) (a : GapTriple)
    (q q' : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (hdist : (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q').1)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m 2 (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m 2 (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1)
    (hcanonical' : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m 2 (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted' : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m 2 (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
      eta.1.1.external.tail.1) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    let s' := trajectory (extendPrefix (directionVectorOfList v'))
    s ∈ firstStructuralPast t m a ↔ s' ∈ firstStructuralPast t m a := by
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have h₁ := sourceCanonical_creationTime_record_eq (rank := 1) eta hm
    (by omega) (by omega) (by omega) q q' hdist hcanonical haccepted
      hcanonical' haccepted'
  have h₂ := sourceCanonical_creationTime_record_eq (rank := 2) eta hm
    (by omega) (by omega) (by omega) q q' hdist hcanonical haccepted
      hcanonical' haccepted'
  have hdata₁ := sourceCanonical_creationTime_data (rank := 1) eta
    (by omega) (by omega) q haccepted
  have hdata₁' := sourceCanonical_creationTime_data (rank := 1) eta
    (by omega) (by omega) q' haccepted'
  have hdata₂ := sourceCanonical_creationTime_data (rank := 2) eta
    (by omega) (by omega) q haccepted
  have hdata₂' := sourceCanonical_creationTime_data (rank := 2) eta
    (by omega) (by omega) q' haccepted'
  have hcount := sourceCanonical_thresholdCount_succ_eq eta q q' hdist
    hcanonical haccepted hcanonical' haccepted'
  have htime := sourceCanonical_creationTime_eq_length eta (by omega) q
    haccepted
  have htime' := sourceCanonical_creationTime_eq_length eta (by omega) q'
    haccepted'
  have hgap := sourceCanonical_lowGapDeficitFailure_iff
    (oldRank := 1) (newRank := 2) eta hm (by omega) (by omega)
      (by omega) (by omega) q q' hdist hcanonical haccepted hcanonical'
      haccepted'
  change
    (s ∈ firstTransitionEvent t m a ∧
        s ∉ firstLowGapFailureEvent t m a) ↔
      (s' ∈ firstTransitionEvent t m a ∧
        s' ∉ firstLowGapFailureEvent t m a)
  simp only [mem_firstTransitionEvent_iff_creationTime,
    mem_firstLowGapFailureEvent_iff_creationTime, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  have hsite₁ : s (creationTimeNat m 1 s) =
      s' (creationTimeNat m 1 s') := by
    simpa only [v, v', s, s'] using h₁.1
  have hsite₂ : s (creationTimeNat m 2 s) =
      s' (creationTimeNat m 2 s') := by
    simpa only [v, v', s, s'] using h₂.1
  have hcount' : thresholdCount s (creationTimeNat m 2 s) (m + 1) =
      thresholdCount s' (creationTimeNat m 2 s') (m + 1) := by
    simpa only [v, v', s, s', htime, htime'] using hcount
  have hgap' : lowGapDeficitFailure s m (creationTimeNat m 1 s)
      (creationTimeNat m 2 s) ↔
      lowGapDeficitFailure s' m (creationTimeNat m 1 s')
        (creationTimeNat m 2 s') := by
    simpa only [v, v', s, s'] using hgap
  have hpair :
      s ∈ pairConfiguration t m a.1.1 (creationTimeNat m 1 s)
          (creationTimeNat m 2 s) ↔
        s' ∈ pairConfiguration t m a.1.1 (creationTimeNat m 1 s')
          (creationTimeNat m 2 s') := by
    constructor
    · rintro ⟨_hc₁, _hc₂, hnext, hdomino, hscale⟩
      refine ⟨hdata₁'.1, hdata₂'.1, ?_, ?_, ?_⟩
      · exact hcount'.symm ▸ hnext
      · simpa only [← hsite₁, ← hsite₂] using hdomino
      · simpa only [← hsite₁, ← hsite₂] using hscale
    · rintro ⟨_hc₁, _hc₂, hnext, hdomino, hscale⟩
      refine ⟨hdata₁.1, hdata₂.1, ?_, ?_, ?_⟩
      · exact hcount' ▸ hnext
      · simpa only [hsite₁, hsite₂] using hdomino
      · simpa only [hsite₁, hsite₂] using hscale
  constructor
  · rintro ⟨hp, hbad⟩
    refine ⟨hpair.mp hp, ?_⟩
    rintro ⟨hp', hgapBad'⟩
    exact hbad ⟨hp, hgap'.mpr hgapBad'⟩
  · rintro ⟨hp', hbad'⟩
    refine ⟨hpair.mpr hp', ?_⟩
    rintro ⟨hp, hgapBad⟩
    exact hbad' ⟨hp', hgap'.mp hgapBad⟩

/-- On a rank-three canonical source atom, the structural second past is
fixed by the distinguished coordinate projection. -/
theorem sourceCanonical_secondStructuralPast_iff
    {t : DominoTiling} {o : Orientation} {m cap : ℕ}
    (eta : SourceSupportedIndex t o m 3) (hm : 1 < m) (a : GapTriple)
    (q q' : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (hdist : (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q').1)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m 3 (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m 3 (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1)
    (hcanonical' : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m 3 (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted' : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m 3 (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
      eta.1.1.external.tail.1) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    let s' := trajectory (extendPrefix (directionVectorOfList v'))
    s ∈ secondStructuralPast t m a ↔ s' ∈ secondStructuralPast t m a := by
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have h₁ := sourceCanonical_creationTime_record_eq (rank := 1) eta hm
    (by omega) (by omega) (by omega) q q' hdist hcanonical haccepted
      hcanonical' haccepted'
  have h₂ := sourceCanonical_creationTime_record_eq (rank := 2) eta hm
    (by omega) (by omega) (by omega) q q' hdist hcanonical haccepted
      hcanonical' haccepted'
  have h₃ := sourceCanonical_creationTime_record_eq (rank := 3) eta hm
    (by omega) (by omega) (by omega) q q' hdist hcanonical haccepted
      hcanonical' haccepted'
  have hdata₁ := sourceCanonical_creationTime_data (rank := 1) eta
    (by omega) (by omega) q haccepted
  have hdata₁' := sourceCanonical_creationTime_data (rank := 1) eta
    (by omega) (by omega) q' haccepted'
  have hdata₂ := sourceCanonical_creationTime_data (rank := 2) eta
    (by omega) (by omega) q haccepted
  have hdata₂' := sourceCanonical_creationTime_data (rank := 2) eta
    (by omega) (by omega) q' haccepted'
  have hdata₃ := sourceCanonical_creationTime_data (rank := 3) eta
    (by omega) (by omega) q haccepted
  have hdata₃' := sourceCanonical_creationTime_data (rank := 3) eta
    (by omega) (by omega) q' haccepted'
  have hcount := sourceCanonical_thresholdCount_succ_eq eta q q' hdist
    hcanonical haccepted hcanonical' haccepted'
  have htime := sourceCanonical_creationTime_eq_length eta (by omega) q
    haccepted
  have htime' := sourceCanonical_creationTime_eq_length eta (by omega) q'
    haccepted'
  have hgap₁ := sourceCanonical_lowGapDeficitFailure_iff
    (oldRank := 1) (newRank := 2) eta hm (by omega) (by omega)
      (by omega) (by omega) q q' hdist hcanonical haccepted hcanonical'
      haccepted'
  have hgap₂ := sourceCanonical_lowGapDeficitFailure_iff
    (oldRank := 2) (newRank := 3) eta hm (by omega) (by omega)
      (by omega) (by omega) q q' hdist hcanonical haccepted hcanonical'
      haccepted'
  change
    (s ∈ secondTransitionEvent t m a ∧
        s ∉ firstLowGapFailureEvent t m a ∪ secondLowGapFailureEvent t m a) ↔
      (s' ∈ secondTransitionEvent t m a ∧
        s' ∉ firstLowGapFailureEvent t m a ∪ secondLowGapFailureEvent t m a)
  simp only [mem_union, mem_secondTransitionEvent_iff_creationTime,
    mem_firstLowGapFailureEvent_iff_creationTime,
    mem_secondLowGapFailureEvent_iff_creationTime, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  have hsite₁ : s (creationTimeNat m 1 s) =
      s' (creationTimeNat m 1 s') := by
    simpa only [v, v', s, s'] using h₁.1
  have hsite₂ : s (creationTimeNat m 2 s) =
      s' (creationTimeNat m 2 s') := by
    simpa only [v, v', s, s'] using h₂.1
  have hsite₃ : s (creationTimeNat m 3 s) =
      s' (creationTimeNat m 3 s') := by
    simpa only [v, v', s, s'] using h₃.1
  have hcount' : thresholdCount s (creationTimeNat m 3 s) (m + 1) =
      thresholdCount s' (creationTimeNat m 3 s') (m + 1) := by
    simpa only [v, v', s, s', htime, htime'] using hcount
  have hgap₁' : lowGapDeficitFailure s m (creationTimeNat m 1 s)
      (creationTimeNat m 2 s) ↔
      lowGapDeficitFailure s' m (creationTimeNat m 1 s')
        (creationTimeNat m 2 s') := by
    simpa only [v, v', s, s'] using hgap₁
  have hgap₂' : lowGapDeficitFailure s m (creationTimeNat m 2 s)
      (creationTimeNat m 3 s) ↔
      lowGapDeficitFailure s' m (creationTimeNat m 2 s')
        (creationTimeNat m 3 s') := by
    simpa only [v, v', s, s'] using hgap₂
  have htriple :
      s ∈ tripleConfiguration t m a.1.1 a.1.2
          (creationTimeNat m 1 s) (creationTimeNat m 2 s)
          (creationTimeNat m 3 s) ↔
        s' ∈ tripleConfiguration t m a.1.1 a.1.2
          (creationTimeNat m 1 s') (creationTimeNat m 2 s')
          (creationTimeNat m 3 s') := by
    constructor
    · rintro ⟨_hc₁, _hc₂, _hc₃, hnext, hdom₁₂, hdom₁₃, hdom₂₃,
          hscale₁, hscale₂⟩
      refine ⟨hdata₁'.1, hdata₂'.1, hdata₃'.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hcount'.symm ▸ hnext
      · simpa only [← hsite₁, ← hsite₂] using hdom₁₂
      · simpa only [← hsite₁, ← hsite₃] using hdom₁₃
      · simpa only [← hsite₂, ← hsite₃] using hdom₂₃
      · simpa only [← hsite₁, ← hsite₂] using hscale₁
      · simpa only [← hsite₂, ← hsite₃] using hscale₂
    · rintro ⟨_hc₁, _hc₂, _hc₃, hnext, hdom₁₂, hdom₁₃, hdom₂₃,
          hscale₁, hscale₂⟩
      refine ⟨hdata₁.1, hdata₂.1, hdata₃.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hcount' ▸ hnext
      · simpa only [hsite₁, hsite₂] using hdom₁₂
      · simpa only [hsite₁, hsite₃] using hdom₁₃
      · simpa only [hsite₂, hsite₃] using hdom₂₃
      · simpa only [hsite₁, hsite₂] using hscale₁
      · simpa only [hsite₂, hsite₃] using hscale₂
  constructor
  · rintro ⟨htri, hbad⟩
    have htri' := htriple.mp htri
    have hfirst : s ∈ pairConfiguration t m a.1.1
        (creationTimeNat m 1 s) (creationTimeNat m 2 s) :=
      (mem_firstTransitionEvent_iff_creationTime t m a s).mp <|
        secondTransitionEvent_subset_first t m a <|
          (mem_secondTransitionEvent_iff_creationTime t m a s).mpr htri
    refine ⟨htri', ?_⟩
    rintro (hfirst' | hsecond')
    · exact hbad (Or.inl ⟨hfirst, hgap₁'.mpr hfirst'.2⟩)
    · exact hbad (Or.inr ⟨htri, hgap₂'.mpr hsecond'.2⟩)
  · rintro ⟨htri', hbad'⟩
    have htri := htriple.mpr htri'
    have hfirst' : s' ∈ pairConfiguration t m a.1.1
        (creationTimeNat m 1 s') (creationTimeNat m 2 s') :=
      (mem_firstTransitionEvent_iff_creationTime t m a s').mp <|
        secondTransitionEvent_subset_first t m a <|
          (mem_secondTransitionEvent_iff_creationTime t m a s').mpr htri'
    refine ⟨htri, ?_⟩
    rintro (hfirst | hsecond)
    · exact hbad' (Or.inl ⟨hfirst', hgap₁'.mp hfirst.2⟩)
    · exact hbad' (Or.inr ⟨htri', hgap₂'.mp hsecond.2⟩)

end

end Erdos1165.HLOZSourceStructuralPastInvariant
