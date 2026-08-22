/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSourceCapAtom

/-!
# One-base support deletion for observable singleton replacements

An observable singleton replacement agrees with its exact pair source on
every insertion coordinate except the exposed domino.  Hence its physical
pair support at the honest raised rank is either the original support or the
original support with that one base deleted.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZPositiveInterfacePairSingleDeletionAtom

open HLOZActualDeltaSelectedProduct
open HLOZPathEvents
open HLOZPositiveInterfaceExternalPairCoordinateRecovery
open HLOZPositiveInterfacePairActualDeltaCapBound
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairSourceCapAtom
open HLOZPositiveInterfacePairSupportActualDeltaAtom
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfaceSupportSelector
open HLOZPositiveInterfacePairWindowTailObservableCap
open HLOZPositiveInterfacePairWindowTailSingleton
open HLOZSourceOrientedThetaAcceptedCreationPath
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PathInsertion PreStoppingFiber StoppedInsertion
open TilingCappedMarginalization
open TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroStaticSupportLocalTimeTransport
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- If two paths have the same external word and the same local times away
from one domino base, their adjacent-row supports agree after erasing that
base. -/
theorem orientedPositiveInterfacePairSupportAt_erase_eq_of_localTime_eq_off
    {t : DominoTiling} {o : Orientation}
    {m externalThreshold width shell : ℕ}
    {sSource sReplacement : WalkPath} {nSource nReplacement : ℕ}
    {z : OrientedTilingTypedExternalWordCode t} (b : Point)
    (hm : 0 < m)
    (hcodeSource : fixedOrientedTypedExternalWordCode t o nSource sSource = z)
    (hcodeReplacement :
      fixedOrientedTypedExternalWordCode t o nReplacement sReplacement = z)
    (houtside : ∀ y, tilingBase t y ≠ b →
      localTime sReplacement nReplacement y =
        localTime sSource nSource y) :
    (orientedPositiveInterfacePairSupportAt t o m externalThreshold width
      shell sReplacement nReplacement).erase b =
      (orientedPositiveInterfacePairSupportAt t o m externalThreshold width
        shell sSource nSource).erase b := by
  classical
  ext c
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hcb, hcReplacement⟩
    refine ⟨hcb, ?_⟩
    rw [orientedPositiveInterfacePairSupportAt,
      Finset.mem_filter] at hcReplacement ⊢
    have hcReplacementCode := hcReplacement.1
    unfold orientedPositiveInterfaceSupportAt at hcReplacementCode
    have hcCode :=
      mem_orientedPositiveInterfaceCodeSupport_iff.mp hcReplacementCode
    rw [hcodeReplacement] at hcCode
    have hcBase : IsTilingBase t c :=
      isTilingBase_of_tilingBase_eq_self t c
        (tilingExternalDomino_is_base t z.start z.retained
          ⟨c, hcCode.1⟩)
    have hendpointBase :
        tilingBase t (orientedDominoEndpoint t o c) = c :=
      tilingBase_orientedDominoEndpoint t o c hcBase
    have hthreshold : c ∉
        (thresholdSites sSource nSource m).image (tilingBase t) := by
      intro hcThreshold
      rcases Finset.mem_image.mp hcThreshold with ⟨y, hy, hyBase⟩
      have hyOutside : tilingBase t y ≠ b := by
        intro hyb
        exact hcb (hyBase ▸ hyb)
      have hyReplacement : y ∈ thresholdSites sReplacement nReplacement m := by
        rw [mem_thresholdSites_iff sReplacement nReplacement m y hm,
          houtside y hyOutside]
        exact (mem_thresholdSites_iff sSource nSource m y hm).mp hy
      exact hcCode.2.2
        (Finset.mem_image.mpr ⟨y, hyReplacement, hyBase⟩)
    have hcSourceBroad : c ∈ orientedPositiveInterfaceSupportAt t o m
        externalThreshold sSource nSource := by
      unfold orientedPositiveInterfaceSupportAt
      apply mem_orientedPositiveInterfaceCodeSupport_iff.mpr
      rw [hcodeSource]
      exact ⟨hcCode.1, hcCode.2.1, hthreshold⟩
    have hendpointOutside :
        tilingBase t (orientedDominoEndpoint t o c) ≠ b := by
      simpa only [hendpointBase] using hcb
    have hrowSource :
        (m - localTime sSource nSource (orientedDominoEndpoint t o c)) /
              width = shell ∨
          (m - localTime sSource nSource (orientedDominoEndpoint t o c)) /
              width = shell + 1 := by
      rw [← houtside (orientedDominoEndpoint t o c) hendpointOutside]
      exact hcReplacement.2
    exact ⟨hcSourceBroad, hrowSource⟩
  · rintro ⟨hcb, hcSource⟩
    refine ⟨hcb, ?_⟩
    rw [orientedPositiveInterfacePairSupportAt,
      Finset.mem_filter] at hcSource ⊢
    have hcSourceCode := hcSource.1
    unfold orientedPositiveInterfaceSupportAt at hcSourceCode
    have hcCode :=
      mem_orientedPositiveInterfaceCodeSupport_iff.mp hcSourceCode
    rw [hcodeSource] at hcCode
    have hcBase : IsTilingBase t c :=
      isTilingBase_of_tilingBase_eq_self t c
        (tilingExternalDomino_is_base t z.start z.retained
          ⟨c, hcCode.1⟩)
    have hendpointBase :
        tilingBase t (orientedDominoEndpoint t o c) = c :=
      tilingBase_orientedDominoEndpoint t o c hcBase
    have hthreshold : c ∉
        (thresholdSites sReplacement nReplacement m).image
          (tilingBase t) := by
      intro hcThreshold
      rcases Finset.mem_image.mp hcThreshold with ⟨y, hy, hyBase⟩
      have hyOutside : tilingBase t y ≠ b := by
        intro hyb
        exact hcb (hyBase ▸ hyb)
      have hySource : y ∈ thresholdSites sSource nSource m := by
        rw [mem_thresholdSites_iff sSource nSource m y hm,
          ← houtside y hyOutside]
        exact (mem_thresholdSites_iff sReplacement nReplacement m y hm).mp hy
      exact hcCode.2.2 (Finset.mem_image.mpr ⟨y, hySource, hyBase⟩)
    have hcReplacementBroad : c ∈ orientedPositiveInterfaceSupportAt t o m
        externalThreshold sReplacement nReplacement := by
      unfold orientedPositiveInterfaceSupportAt
      apply mem_orientedPositiveInterfaceCodeSupport_iff.mpr
      rw [hcodeReplacement]
      exact ⟨hcCode.1, hcCode.2.1, hthreshold⟩
    have hendpointOutside :
        tilingBase t (orientedDominoEndpoint t o c) ≠ b := by
      simpa only [hendpointBase] using hcb
    have hrowReplacement :
        (m - localTime sReplacement nReplacement
          (orientedDominoEndpoint t o c)) / width = shell ∨
          (m - localTime sReplacement nReplacement
            (orientedDominoEndpoint t o c)) / width = shell + 1 := by
      rw [houtside (orientedDominoEndpoint t o c) hendpointOutside]
      exact hcSource.2
    exact ⟨hcReplacementBroad, hrowReplacement⟩

/-- The dominant pair support has the same one-base deletion invariance as
the raw pair support.  Dominance is fixed by the external word, so equal
external codes transport the canonical tie-breaking predicate as well. -/
theorem orientedDominantPositiveInterfacePairSupportAt_erase_eq_of_localTime_eq_off
    {t : DominoTiling} {o : Orientation}
    {m externalThreshold width shell : ℕ}
    {sSource sReplacement : WalkPath} {nSource nReplacement : ℕ}
    {z : OrientedTilingTypedExternalWordCode t} (b : Point)
    (hm : 0 < m)
    (hcodeSource : fixedOrientedTypedExternalWordCode t o nSource sSource = z)
    (hcodeReplacement :
      fixedOrientedTypedExternalWordCode t o nReplacement sReplacement = z)
    (houtside : ∀ y, tilingBase t y ≠ b →
      localTime sReplacement nReplacement y =
        localTime sSource nSource y) :
    (PositiveInterfacePairSupportAt t o m externalThreshold width shell
      sReplacement nReplacement).erase b =
      (PositiveInterfacePairSupportAt t o m externalThreshold width shell
        sSource nSource).erase b := by
  classical
  have hraw :=
    orientedPositiveInterfacePairSupportAt_erase_eq_of_localTime_eq_off
      (m := m) (externalThreshold := externalThreshold) (width := width)
      (shell := shell) b hm hcodeSource hcodeReplacement houtside
  ext c
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hcb, hcReplacement⟩
    have hcReplacement' :=
      (HLOZDominantPositiveInterfaceSupportSelector.mem_orientedDominantPositiveInterfacePairSupportAt_iff
        t o m externalThreshold width shell sReplacement nReplacement c).mp
        hcReplacement
    refine ⟨hcb,
      (HLOZDominantPositiveInterfaceSupportSelector.mem_orientedDominantPositiveInterfacePairSupportAt_iff
        t o m externalThreshold width shell sSource nSource c).mpr ⟨?_, ?_⟩⟩
    · have hcErase :
          c ∈ (orientedPositiveInterfacePairSupportAt t o m externalThreshold
            width shell sReplacement nReplacement).erase b :=
        Finset.mem_erase.mpr ⟨hcb, hcReplacement'.1⟩
      rw [hraw] at hcErase
      exact (Finset.mem_erase.mp hcErase).2
    · have hcDominant := hcReplacement'.2
      unfold HLOZDominantPositiveInterfaceSupportSelector.orientedEndpointCanonicallyDominantAt at hcDominant ⊢
      rw [hcodeReplacement] at hcDominant
      rw [hcodeSource]
      exact hcDominant
  · rintro ⟨hcb, hcSource⟩
    have hcSource' :=
      (HLOZDominantPositiveInterfaceSupportSelector.mem_orientedDominantPositiveInterfacePairSupportAt_iff
        t o m externalThreshold width shell sSource nSource c).mp hcSource
    refine ⟨hcb,
      (HLOZDominantPositiveInterfaceSupportSelector.mem_orientedDominantPositiveInterfacePairSupportAt_iff
        t o m externalThreshold width shell sReplacement nReplacement c).mpr
        ⟨?_, ?_⟩⟩
    · have hcErase :
          c ∈ (orientedPositiveInterfacePairSupportAt t o m externalThreshold
            width shell sSource nSource).erase b :=
        Finset.mem_erase.mpr ⟨hcb, hcSource'.1⟩
      rw [← hraw] at hcErase
      exact (Finset.mem_erase.mp hcErase).2
    · have hcDominant := hcSource'.2
      unfold HLOZDominantPositiveInterfaceSupportSelector.orientedEndpointCanonicallyDominantAt at hcDominant ⊢
      rw [hcodeSource] at hcDominant
      rw [hcodeReplacement]
      exact hcDominant

/-- A finite support whose erasure agrees with the erasure of a support
containing `b` is either that support or its one-base deletion. -/
theorem eq_or_eq_erase_of_erase_eq {S T : Finset Point} {b : Point}
    (hbS : b ∈ S) (h : T.erase b = S.erase b) :
    T = S ∨ T = S.erase b := by
  classical
  by_cases hbT : b ∈ T
  · left
    ext c
    by_cases hcb : c = b
    · subst c
      simp only [hbT, hbS]
    · constructor
      · intro hcT
        have hcEraseT : c ∈ T.erase b := Finset.mem_erase.mpr ⟨hcb, hcT⟩
        have hcEraseS : c ∈ S.erase b := h ▸ hcEraseT
        exact (Finset.mem_erase.mp hcEraseS).2
      · intro hcS
        have hcEraseS : c ∈ S.erase b := Finset.mem_erase.mpr ⟨hcb, hcS⟩
        have hcEraseT : c ∈ T.erase b := h.symm ▸ hcEraseS
        exact (Finset.mem_erase.mp hcEraseT).2
  · right
    rw [← Finset.erase_eq_self.mpr hbT, h]

/-- The observable raised-rank atom allows precisely the original pair
support and its deletion at the exposed base. -/
def positiveInterfaceExternalPairSingleDeletionRankAtom
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell delta : ℕ)
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) : Set WalkPath :=
  positiveInterfaceExternalPairRankAtom t o m k externalThreshold width shell
      delta eta ∪
    orientedExternalAllCreationSupportTraceAtom t o m (k + delta)
      (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
      eta.1.1 (eta.1.2.erase b.1.1)

theorem measurableSet_positiveInterfaceExternalPairSingleDeletionRankAtom
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell delta : ℕ)
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) :
    MeasurableSet (positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
      externalThreshold width shell delta eta b) := by
  apply MeasurableSet.union
  · exact measurableSet_positiveInterfaceExternalPairRankAtom t o m k
      externalThreshold width shell delta eta
  · apply measurableSet_orientedExternalAllCreationSupportTraceAtom
    exact measurable_natIndexed (creationTimeNat m (k + delta))
      (measurable_creationTimeNat m (k + delta))
      (fun n s => PositiveInterfacePairSupportAt t o m
        externalThreshold width shell s n)
      (HLOZDominantPositiveInterfaceSupportSelector.measurable_orientedDominantPositiveInterfacePairSupportAt t o m
        externalThreshold width shell)

/-- Every observable singleton replacement is visible at its honest raised
rank in the source pair atom, up to deletion of the one exposed base. -/
theorem singletonPairObservableActualDeltaCap_subset_singleDeletionRankAtom
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (HLOZProposition48Candidates.shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (hm : 1 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (delta : SourceActualDeltaIndex (singletonPairFiber eta b)) :
    singletonPairObservableActualDeltaCap eta b cap threshold bound delta ⊆
      positiveInterfaceExternalPairSingleDeletionRankAtom t o m k
        externalThreshold (HLOZProposition48Candidates.shellWidth48 m) shell
        (delta : ℕ) eta b := by
  classical
  intro s hs
  rcases hs with ⟨hvalid, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨qAccepted, hq⟩
  let data := singletonPairFiber eta b
  let qReplacement := qAccepted.1
  have hpred := qAccepted.2.1
  have hacceptedReplacement := qAccepted.2.2
  change singletonPairObservableActualDeltaPredicate eta b cap threshold bound
      delta qReplacement at hpred
  unfold singletonPairObservableActualDeltaPredicate
    actualDeltaSelectedPredicate at hpred
  have hselected := hpred.1
  change singletonPairObservableSelected eta b cap threshold bound
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point)) qReplacement).1) at hselected
  rcases hselected with
    ⟨_hsingletonSelected, qSource, hsourcePredicate, hsplitSource⟩
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained ({b.1.1} : Finset Point)
  let vSource := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j => (qSource j : ℕ))
      eta.1.1.tail.1
  let vReplacement := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j => (qReplacement j : ℕ))
      eta.1.1.tail.1
  let sSource := trajectory
    (extendPrefix (directionVectorOfList vSource))
  let sReplacement := trajectory
    (extendPrefix (directionVectorOfList vReplacement))
  have hdist :
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
        qSource).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
        qReplacement).1 := by
    simpa only [D] using hsplitSource
  have hfactor := positiveInterfaceExternalPairSourcePredicate_factorization
    eta (by omega) hk hfixedPos cap threshold bound qSource
  dsimp only at hfactor
  have hsourceAcceptedPair := hfactor.mpr hsourcePredicate
  have hsourceAccepted := hsourceAcceptedPair.2
  have hltSource : vSource.length <
      externalCoordinateCutoff eta.1.1
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap) := by
    let dummy : TilingCreationFavoriteData :=
      ((∅, ∅), (eta.1.1.start, eta.1.1.start))
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy)
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap) qSource
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hcreationSource : ThresholdCreation sSource m k vSource.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m k
      (externalCoordinateCutoff eta.1.1
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap))
      vSource.length _ hltSource).mp
    exact hsourceAccepted
  have htimeSource : creationTimeNat m k sSource = vSource.length :=
    creationTimeNat_eq_of_creation hcreationSource
  have homegaSource : extendPrefix (directionVectorOfList vSource) ∈
      prefixedTilingStoppedInsertionAtom
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1
            ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)))
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j => (qSource j : ℕ)) eta.1.1.tail.1 := by
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      (isFiniteStoppingTime_truncatedLevelTime m k
        (externalCoordinateCutoff eta.1.1
          ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)))
      _ _ _ _ _ _ hsourceAccepted]
    change stepPrefix vSource.length
      (extendPrefix (directionVectorOfList vSource)) =
        directionVectorOfList vSource
    rw [stepPrefix_extendPrefix]
  have hsourceCap : sSource ∈
      positiveInterfaceExternalPairSourceCap eta cap threshold bound := by
    refine ⟨trajectory_mem_validStepWalk _, ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨⟨qSource, hsourcePredicate, hsourceAccepted⟩, ?_⟩
    simpa only [sSource, stepsOfWalk_trajectory] using homegaSource
  have hsourceRank :=
    positiveInterfaceExternalPairSourceCap_subset_pairRankAtom eta hm hk cap
      threshold bound hsourceCap
  rw [positiveInterfaceExternalPairRankAtom,
    orientedExternalAllCreationSupportTraceAtom_eq] at hsourceRank
  simp only [Nat.add_zero] at hsourceRank
  have hcodeSource : fixedOrientedTypedExternalWordCode t o
      vSource.length sSource = eta.1.1 := by
    rw [← htimeSource]
    exact hsourceRank.2.2.1
  have hsupportSource : PositiveInterfacePairSupportAt t o m
      externalThreshold (HLOZProposition48Candidates.shellWidth48 m) shell
        sSource vSource.length = eta.1.2 := by
    rw [← htimeSource]
    exact hsourceRank.2.2.2
  have heta_nonempty :
      (allRepresentedExternalCreationTraceAtom t o m k eta.1.1).Nonempty := by
    rcases eta.2 with ⟨s0, hs0⟩
    rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs0
    exact ⟨s0, hs0.1, hs0.2.1, hs0.2.2.1⟩
  let etaAll : TilingOrientedAllRepresentedExternalFiber.SupportedIndex
      t o m k := ⟨eta.1.1, heta_nonempty⟩
  have hcodeReplacement : fixedOrientedTypedExternalWordCode t o
      vReplacement.length sReplacement = eta.1.1 := by
    simpa only [etaAll, sReplacement, vReplacement] using
      (fixedCode_prefixedInsertion etaAll hm hk
        (fun j => (qReplacement j : ℕ)))
  have houtside : ∀ y, tilingBase t y ≠ b.1.1 →
      localTime sReplacement vReplacement.length y =
        localTime sSource vSource.length y := by
    intro y hy
    exact prefixedTilingLocalTime_eq_of_base_not_staticSupport
      eta.1.1.initial t eta.1.1.start eta.1.1.retained eta.1.1.tail
      ({b.1.1} : Finset Point) qSource qReplacement rfl hdist y
        (by simpa only [Finset.mem_singleton] using hy)
  have herase :
      (PositiveInterfacePairSupportAt t o m externalThreshold
        (HLOZProposition48Candidates.shellWidth48 m) shell sReplacement
          vReplacement.length).erase b.1.1 = eta.1.2.erase b.1.1 := by
    have h :=
      orientedDominantPositiveInterfacePairSupportAt_erase_eq_of_localTime_eq_off
        (m := m) (externalThreshold := externalThreshold)
        (width := HLOZProposition48Candidates.shellWidth48 m)
        (shell := shell) b.1.1 (by omega) hcodeSource hcodeReplacement
          houtside
    rw [hsupportSource] at h
    exact h
  have hbSupport : b.1.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b.1).1
      b.2
  have hsupportReplacement :
      PositiveInterfacePairSupportAt t o m externalThreshold
          (HLOZProposition48Candidates.shellWidth48 m) shell sReplacement
            vReplacement.length = eta.1.2 ∨
        PositiveInterfacePairSupportAt t o m externalThreshold
          (HLOZProposition48Candidates.shellWidth48 m) shell sReplacement
            vReplacement.length = eta.1.2.erase b.1.1 :=
    eq_or_eq_erase_of_erase_eq hbSupport herase
  have hltReplacement : vReplacement.length <
      externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    let dummy : TilingCreationFavoriteData :=
      ((∅, ∅), (eta.1.1.start, eta.1.1.start))
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) qReplacement
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hcreationReplacement : ThresholdCreation sReplacement m
      (k + (delta : ℕ)) vReplacement.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m
      (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
      vReplacement.length _ hltReplacement).mp
    exact hacceptedReplacement
  have hp : pathPrefix s vReplacement.length =
      pathPrefix sReplacement vReplacement.length := by
    have hp' := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
      eta.1.1.initial.1 eta.1.1.start eta.1.1.retained
      (fun j => (qReplacement j : ℕ)) eta.1.1.tail.1 (stepsOfWalk s) hq
    change trajectory (stepsOfWalk s) = s at hvalid
    rw [hvalid] at hp'
    simpa only [sReplacement, vReplacement] using hp'
  have hcreationS : ThresholdCreation s m (k + (delta : ℕ))
      vReplacement.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp
      (Nat.le_refl vReplacement.length)).mpr hcreationReplacement
  have htimeS : creationTimeNat m (k + (delta : ℕ)) s =
      vReplacement.length := creationTimeNat_eq_of_creation hcreationS
  have hcodeS : fixedOrientedTypedExternalWordCode t o vReplacement.length s =
      eta.1.1 :=
    (fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp).trans
      hcodeReplacement
  have hsupportPrefix :=
    HLOZDominantPositiveInterfaceSupportSelector.orientedDominantPositiveInterfacePairSupportAt_prefix_invariant t o m
      externalThreshold (HLOZProposition48Candidates.shellWidth48 m) shell hp
  have hsupportS :
      PositiveInterfacePairSupportAt t o m externalThreshold
          (HLOZProposition48Candidates.shellWidth48 m) shell s
            vReplacement.length = eta.1.2 ∨
        PositiveInterfacePairSupportAt t o m externalThreshold
          (HLOZProposition48Candidates.shellWidth48 m) shell s
            vReplacement.length = eta.1.2.erase b.1.1 :=
    hsupportReplacement.elim
      (fun h => Or.inl (hsupportPrefix.trans h))
      (fun h => Or.inr (hsupportPrefix.trans h))
  rw [positiveInterfaceExternalPairSingleDeletionRankAtom]
  rcases hsupportS with hsupportS | hsupportS
  · left
    rw [positiveInterfaceExternalPairRankAtom,
      orientedExternalAllCreationSupportTraceAtom_eq]
    refine ⟨hvalid, ⟨vReplacement.length, hcreationS.1⟩, ?_, ?_⟩
    · rw [htimeS]
      exact hcodeS
    · rw [htimeS]
      exact hsupportS
  · right
    rw [orientedExternalAllCreationSupportTraceAtom_eq]
    refine ⟨hvalid, ⟨vReplacement.length, hcreationS.1⟩, ?_, ?_⟩
    · rw [htimeS]
      exact hcodeS
    · rw [htimeS]
      exact hsupportS

end

end Erdos1165.HLOZPositiveInterfacePairSingleDeletionAtom
