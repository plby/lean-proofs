/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceExternalPairCoordinateRecovery
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSupportActualDeltaWalkCap
import ErdosProblems.Erdos1165.TilingShellZeroStaticSupportLocalTimeTransport

/-!
# Observable atoms for support-preserving positive-interface replacements

The support-preserving replacement screen keeps the exact adjacent pair
support visible at the honest raised creation rank.  This supplies the
pairwise-disjoint atoms required by the variable-rank harmonic summation.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZPositiveInterfacePairSupportActualDeltaAtom

open HLOZDominantPositiveInterfaceSupportSelector
open HLOZActualDeltaSelectedScreenedProduct
open HLOZPositiveInterfaceExternalPairCoordinateRecovery
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairSupportActualDeltaWalkCap
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairSupportPreservingBound
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfacePairWeightedScreen
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZPositiveInterfaceSupportSelector
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open HLOZSourceOrientedThetaAcceptedCreationPath
open HLOZPathEvents
open LazyDecomposition PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open StoppedInsertion
open TilingCappedMarginalization
open TilingDistinguishedTraceInvariant TilingInsertedLocalTime
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroStaticSupportLocalTimeTransport
open TilingLazyDecomposition
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- The exact external-word and adjacent-pair support atom at the honest
raised rank. -/
def positiveInterfaceExternalPairRankAtom
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell delta : ℕ)
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) : Set WalkPath :=
  orientedExternalAllCreationSupportTraceAtom t o m (k + delta)
    (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
    eta.1.1 eta.1.2

theorem measurableSet_positiveInterfaceExternalPairRankAtom
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell delta : ℕ)
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) :
    MeasurableSet (positiveInterfaceExternalPairRankAtom t o m k
      externalThreshold width shell delta eta) := by
  apply measurableSet_orientedExternalAllCreationSupportTraceAtom
  exact measurable_natIndexed (creationTimeNat m (k + delta))
    (measurable_creationTimeNat m (k + delta))
    (fun n s => orientedDominantPositiveInterfacePairSupportAt t o m
      externalThreshold width shell s n)
    (measurable_orientedDominantPositiveInterfacePairSupportAt t o m
      externalThreshold width shell)

/-- At a fixed raised rank, distinct source histories have disjoint exact
external-word/support atoms. -/
theorem pairwise_disjoint_positiveInterfaceExternalPairRankAtom
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell delta : ℕ) :
    Pairwise fun eta eta' : PositiveInterfaceExternalPairSupportedIndex
        t o m k externalThreshold width shell =>
      Disjoint
        (positiveInterfaceExternalPairRankAtom t o m k externalThreshold
          width shell delta eta)
        (positiveInterfaceExternalPairRankAtom t o m k externalThreshold
          width shell delta eta') := by
  intro eta eta' hne
  rw [Set.disjoint_left]
  intro s hs hs'
  rw [positiveInterfaceExternalPairRankAtom,
    orientedExternalAllCreationSupportTraceAtom_eq] at hs hs'
  apply hne
  apply Subtype.ext
  exact Prod.ext (hs.2.2.1.symm.trans hs'.2.2.1)
    (hs.2.2.2.symm.trans hs'.2.2.2)

/-- If the external word is fixed, local times outside `S` are unchanged,
and every member of `S` remains strictly below the threshold in the same
two physical rows, then the replacement pair support is exactly `S`. -/
theorem orientedPositiveInterfacePairSupportAt_eq_of_staticSupport
    {t : DominoTiling} {o : Orientation}
    {m externalThreshold width shell : ℕ}
    {sSource sReplacement : WalkPath} {nSource nReplacement : ℕ}
    {z : OrientedTilingTypedExternalWordCode t} {S : Finset Point}
    (hm : 0 < m)
    (hcodeSource : fixedOrientedTypedExternalWordCode t o nSource sSource = z)
    (hcodeReplacement :
      fixedOrientedTypedExternalWordCode t o nReplacement sReplacement = z)
    (hsourceSupport : PositiveInterfacePairSupportAt t o m
      externalThreshold width shell sSource nSource = S)
    (houtside : ∀ y, tilingBase t y ∉ S →
      localTime sReplacement nReplacement y =
        localTime sSource nSource y)
    (hinsideBelow : ∀ b ∈ S,
      localTime sReplacement nReplacement b < m ∧
        localTime sReplacement nReplacement (tilingPartner t b) < m)
    (hinsideRow : ∀ b ∈ S,
      (m - localTime sReplacement nReplacement
          (orientedDominoEndpoint t o b)) / width = shell ∨
        (m - localTime sReplacement nReplacement
          (orientedDominoEndpoint t o b)) / width = shell + 1) :
    PositiveInterfacePairSupportAt t o m externalThreshold width shell
        sReplacement nReplacement = S := by
  classical
  apply Finset.Subset.antisymm
  · intro b hbReplacement
    have hbReplacement' :=
      (mem_orientedDominantPositiveInterfacePairSupportAt_iff t o m
        externalThreshold width shell sReplacement nReplacement b).mp
        hbReplacement
    by_contra hbNot
    have hbReplacementCode :=
      (Finset.mem_filter.mp hbReplacement'.1).1
    unfold orientedPositiveInterfaceSupportAt at hbReplacementCode
    have hbCode :=
      mem_orientedPositiveInterfaceCodeSupport_iff.mp hbReplacementCode
    rw [hcodeReplacement] at hbCode
    have hbBase : IsTilingBase t b :=
      isTilingBase_of_tilingBase_eq_self t b
        (tilingExternalDomino_is_base t z.start z.retained
          ⟨b, hbCode.1⟩)
    have hendpointBase : tilingBase t (orientedDominoEndpoint t o b) = b :=
      tilingBase_orientedDominoEndpoint t o b hbBase
    have hthreshold : b ∉
        (thresholdSites sSource nSource m).image (tilingBase t) := by
      intro hbThreshold
      rcases Finset.mem_image.mp hbThreshold with ⟨y, hy, hyBase⟩
      have hyOutside : tilingBase t y ∉ S := by simpa only [hyBase] using hbNot
      have hyReplacement : y ∈ thresholdSites sReplacement nReplacement m := by
        rw [mem_thresholdSites_iff sReplacement nReplacement m y hm,
          houtside y hyOutside]
        exact (mem_thresholdSites_iff sSource nSource m y hm).mp hy
      exact hbCode.2.2 (Finset.mem_image.mpr ⟨y, hyReplacement, hyBase⟩)
    have hbSourceBroad : b ∈ orientedPositiveInterfaceSupportAt t o m
        externalThreshold sSource nSource := by
      unfold orientedPositiveInterfaceSupportAt
      apply mem_orientedPositiveInterfaceCodeSupport_iff.mpr
      rw [hcodeSource]
      exact ⟨hbCode.1, hbCode.2.1, hthreshold⟩
    have hendpointOutside :
        tilingBase t (orientedDominoEndpoint t o b) ∉ S := by
      simpa only [hendpointBase] using hbNot
    have hrowSource :
        (m - localTime sSource nSource (orientedDominoEndpoint t o b)) /
              width = shell ∨
          (m - localTime sSource nSource (orientedDominoEndpoint t o b)) /
              width = shell + 1 := by
      rw [← houtside (orientedDominoEndpoint t o b) hendpointOutside]
      exact (Finset.mem_filter.mp hbReplacement'.1).2
    have hbSource : b ∈ orientedPositiveInterfacePairSupportAt t o m
        externalThreshold width shell sSource nSource := by
      rw [orientedPositiveInterfacePairSupportAt, Finset.mem_filter]
      exact ⟨hbSourceBroad, hrowSource⟩
    have hdominantSource : orientedEndpointCanonicallyDominantAt t o sSource
        nSource b := by
      have hdominantReplacement := hbReplacement'.2
      unfold orientedEndpointCanonicallyDominantAt at hdominantReplacement ⊢
      rw [hcodeReplacement] at hdominantReplacement
      rw [hcodeSource]
      exact hdominantReplacement
    exact hbNot (hsourceSupport ▸
      (mem_orientedDominantPositiveInterfacePairSupportAt_iff t o m
        externalThreshold width shell sSource nSource b).mpr
          ⟨hbSource, hdominantSource⟩)
  · intro b hbS
    have hbSourceDominant : b ∈ PositiveInterfacePairSupportAt t o m
        externalThreshold width shell sSource nSource := by
      rw [hsourceSupport]
      exact hbS
    rcases
        (mem_orientedDominantPositiveInterfacePairSupportAt_iff t o m
          externalThreshold width shell sSource nSource b).mp
          hbSourceDominant with
      ⟨hbSource, hdominantSource⟩
    rw [orientedPositiveInterfacePairSupportAt, Finset.mem_filter] at hbSource
    have hbSourceCode := hbSource.1
    unfold orientedPositiveInterfaceSupportAt at hbSourceCode
    have hbCode := mem_orientedPositiveInterfaceCodeSupport_iff.mp hbSourceCode
    rw [hcodeSource] at hbCode
    have hbBase : IsTilingBase t b :=
      isTilingBase_of_tilingBase_eq_self t b
        (tilingExternalDomino_is_base t z.start z.retained
          ⟨b, hbCode.1⟩)
    have hbNotThreshold : b ∉
        (thresholdSites sReplacement nReplacement m).image
          (tilingBase t) := by
      intro hbThreshold
      rcases Finset.mem_image.mp hbThreshold with ⟨y, hy, hyBase⟩
      have hyLevel :=
        (mem_thresholdSites_iff sReplacement nReplacement m y hm).mp hy
      rcases point_eq_tilingBase_or_partner_base t y with hyEq | hyEq
      · have : y = b := hyEq.trans hyBase
        subst y
        exact (Nat.not_le_of_lt (hinsideBelow b hbS).1) hyLevel
      · have : y = tilingPartner t b := by simpa only [hyBase] using hyEq
        subst y
        exact (Nat.not_le_of_lt (hinsideBelow b hbS).2) hyLevel
    apply (mem_orientedDominantPositiveInterfacePairSupportAt_iff t o m
      externalThreshold width shell sReplacement nReplacement b).mpr
    constructor
    · rw [orientedPositiveInterfacePairSupportAt, Finset.mem_filter]
      refine ⟨?_, hinsideRow b hbS⟩
      unfold orientedPositiveInterfaceSupportAt
      apply mem_orientedPositiveInterfaceCodeSupport_iff.mpr
      rw [hcodeReplacement]
      exact ⟨hbCode.1, hbCode.2.1, hbNotThreshold⟩
    · unfold orientedEndpointCanonicallyDominantAt at hdominantSource ⊢
      rw [hcodeSource] at hdominantSource
      rw [hcodeReplacement]
      exact hdominantSource

/-- Every support-screened actual-delta cap lies in its exact observable
external-word/support atom at the honest raised rank. -/
theorem positiveInterfaceExternalPairSupportActualDeltaCap_subset_rankAtom
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m) (hk : 0 < k) (cap : ℕ)
    (arith : PositiveInterfaceExternalPairArithmetic eta cap)
    (delta : SourceActualDeltaIndex
      (PositiveInterfaceExternalPairFiber eta)) :
    positiveInterfaceExternalPairSupportActualDeltaCap eta cap delta ⊆
      positiveInterfaceExternalPairRankAtom t o m k externalThreshold width
        shell (delta : ℕ) eta := by
  classical
  intro s hs
  rcases hs with ⟨hvalid, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨qAccepted, hq⟩
  let data := PositiveInterfaceExternalPairFiber eta
  let qReplacement := qAccepted.1
  have hpred := qAccepted.2.1
  have hacceptedReplacement := qAccepted.2.2
  change actualDeltaSelectedScreenedPredicate data
      (positiveInterfaceExternalPairSelected eta) cap
      (positiveInterfaceExternalPairReplacementScreen eta cap) delta
      qReplacement at hpred
  rcases hpred with
    ⟨hselected, ellReplacement, ⟨hdelta, hreplacementScreen⟩,
      htotalReplacementAway⟩
  change positiveInterfaceExternalPairSelected eta cap
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) qReplacement).1) at hselected
  rcases hselected with ⟨aSource, ellSource, hatomSource, hacceptedSource,
    _hbaseSource, _htotalSourceAway⟩
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  let qSource := (splitTilingCoordinatesEquiv t eta.1.1.start
      eta.1.1.retained D).symm
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
      qReplacement).1, aSource)
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
    simp only [qSource, Equiv.apply_symm_apply]
  have hltSource : vSource.length <
      externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    let dummy : TilingCreationFavoriteData :=
      ((∅, ∅), (eta.1.1.start, eta.1.1.start))
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) qSource
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hltReplacement : vReplacement.length <
      externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    let dummy : TilingCreationFavoriteData :=
      ((∅, ∅), (eta.1.1.start, eta.1.1.start))
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) qReplacement
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hcreationSource : ThresholdCreation sSource m k vSource.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m k
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
      vSource.length _ hltSource).mp
    exact hacceptedSource
  have htimeSource : creationTimeNat m k sSource = vSource.length :=
    creationTimeNat_eq_of_creation hcreationSource
  rcases hatomSource with ⟨favorite, hatomSource⟩
  have homegaSource : extendPrefix (directionVectorOfList vSource) ∈
      prefixedTilingStoppedInsertionAtom
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j => (qSource j : ℕ)) eta.1.1.tail.1 := by
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      (isFiniteStoppingTime_truncatedLevelTime m k
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      _ _ _ _ _ _ hacceptedSource]
    change stepPrefix vSource.length
      (extendPrefix (directionVectorOfList vSource)) =
        directionVectorOfList vSource
    rw [stepPrefix_extendPrefix]
  have hsourceAtom : sSource ∈
      orientedExternalAllCreationSupportTraceAtom t o m k
        (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
        eta.1.1 eta.1.2 := by
    apply Set.mem_iUnion.mpr
    exact ⟨favorite, hatomSource homegaSource⟩
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hsourceAtom
  have hcodeSource : fixedOrientedTypedExternalWordCode t o
      vSource.length sSource = eta.1.1 := by
    rw [← htimeSource]
    exact hsourceAtom.2.2.1
  have hsupportSource : PositiveInterfacePairSupportAt t o m
      externalThreshold width shell sSource vSource.length = eta.1.2 := by
    rw [← htimeSource]
    exact hsourceAtom.2.2.2
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
  have htotalReplacement : ∀ c : PositiveInterfaceExternalPairCoordinate eta,
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j => (qReplacement j : ℕ)) c.1 = (ellReplacement c : ℕ) := by
    intro c
    exact (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
      eta.1.1.retained D qReplacement c).symm.trans
        (by simpa only [D] using htotalReplacementAway c)
  have hpathReplacement : finitePathList
      (pathPrefix sReplacement vReplacement.length) =
      prefixedTilingPrefixPointPath eta.1.1.initial.1 eta.1.1.start
        (tilingInsertGapVector t eta.1.1.start eta.1.1.retained
          (fun j => (qReplacement j : ℕ)))
        (positiveInterfaceExternalPairTerminal eta) := by
    rw [← positiveInterfaceExternalPairTerminal_eq_coordinates eta
      (fun j => (qReplacement j : ℕ))]
    exact finitePathList_prefixedTilingInsertionPrefix eta.1.1.initial t
      eta.1.1.start eta.1.1.retained
      (fun j => (qReplacement j : ℕ)) eta.1.1.tail rfl
  have hinsideBelow : ∀ b ∈ eta.1.2,
      localTime sReplacement vReplacement.length b < m ∧
        localTime sReplacement vReplacement.length (tilingPartner t b) < m := by
    intro b hbS
    let c := supportAwayChosen t eta.1.1.start eta.1.1.retained eta.1.2
      data.support_represented b hbS
    have hcBase : c.1.1 = b := supportAwayChosen_base t eta.1.1.start
      eta.1.1.retained eta.1.2 data.support_represented b hbS
    have hcSafe : (ellReplacement c : ℕ) ∈
        positiveInterfaceExternalPairBaseWindow eta cap c := by
      rcases hreplacementScreen c with hcUpper | hcLower
      · exact hcUpper.2
      · exact positiveInterfaceExternalPairLower_mem_baseWindow eta cap arith
          c (ellReplacement c) hcLower
    unfold positiveInterfaceExternalPairBaseWindow at hcSafe
    rw [Finset.mem_range] at hcSafe
    have hcMax : prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1
          eta.1.1.start eta.1.1.retained
          (positiveInterfaceExternalPairTerminal eta) c.1 +
        (ellReplacement c : ℕ) < m := by
      omega
    have hbaseLocal : localTime sReplacement vReplacement.length c.1.1 =
        prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
            eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
            c.1.1 + (ellReplacement c : ℕ) := by
      rw [localTime_eq_listLocalTime, hpathReplacement,
        prefixedTilingInsertedPrefix_localTime_at_dominoPoint
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (fun j => (qReplacement j : ℕ))
          (positiveInterfaceExternalPairTerminal eta) c.1 c.1.1
          (tilingExternalDomino_isBase t eta.1.1.start
            eta.1.1.retained c.1), htotalReplacement c]
    have hpartnerLocal : localTime sReplacement vReplacement.length
          (tilingPartner t c.1.1) =
        prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
            eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
            (tilingPartner t c.1.1) + (ellReplacement c : ℕ) := by
      rw [localTime_eq_listLocalTime, hpathReplacement,
        prefixedTilingInsertedPrefix_localTime_at_dominoPoint
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (fun j => (qReplacement j : ℕ))
          (positiveInterfaceExternalPairTerminal eta) c.1
          (tilingPartner t c.1.1)
          (tilingPartner_ofExternalDomino_has_base t eta.1.1.start
            eta.1.1.retained c.1), htotalReplacement c]
    unfold prefixedTilingFixedBoundaryDominoMax at hcMax
    constructor
    · rw [← hcBase, hbaseLocal]
      omega
    · rw [← hcBase, hpartnerLocal]
      omega
  have hinsideRow : ∀ b ∈ eta.1.2,
      (m - localTime sReplacement vReplacement.length
          (orientedDominoEndpoint t o b)) / width = shell ∨
        (m - localTime sReplacement vReplacement.length
          (orientedDominoEndpoint t o b)) / width = shell + 1 := by
    intro b hbS
    let c := supportAwayChosen t eta.1.1.start eta.1.1.retained eta.1.2
      data.support_represented b hbS
    have hcBase : c.1.1 = b := supportAwayChosen_base t eta.1.1.start
      eta.1.1.retained eta.1.2 data.support_represented b hbS
    have hlocal :=
      positiveInterfaceExternalPairCanonical_orientedEndpointLocalTime_eq
        eta hm hk qReplacement c
    change localTime sReplacement vReplacement.length
        (orientedDominoEndpoint t o c.1.1) =
      Fintype.card (TilingCoordinatesAt t eta.1.1.start
          eta.1.1.retained c.1) +
        tilingAwayTotal t eta.1.1.start eta.1.1.retained D
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
            qReplacement).2) c at hlocal
    rw [htotalReplacementAway c] at hlocal
    rcases hreplacementScreen c with hcUpper | hcLower
    · right
      unfold positiveInterfaceExternalPairUpper at hcUpper
      rw [mem_acceptedPhysicalDeficitFailureWindow] at hcUpper
      rw [← hcBase, hlocal]
      exact hcUpper.1.2
    · left
      unfold positiveInterfaceExternalPairLower at hcLower
      rw [mem_acceptedPhysicalDeficitFailureWindow] at hcLower
      rw [← hcBase, hlocal]
      exact hcLower.2
  have houtside : ∀ y, tilingBase t y ∉ eta.1.2 →
      localTime sReplacement vReplacement.length y =
        localTime sSource vSource.length y := by
    intro y hy
    exact prefixedTilingLocalTime_eq_of_base_not_staticSupport
      eta.1.1.initial t eta.1.1.start eta.1.1.retained eta.1.1.tail
      eta.1.2 qSource qReplacement rfl hdist y hy
  have hsupportReplacement : PositiveInterfacePairSupportAt t o m
      externalThreshold width shell sReplacement vReplacement.length =
        eta.1.2 :=
    orientedPositiveInterfacePairSupportAt_eq_of_staticSupport (by omega)
      hcodeSource hcodeReplacement hsupportSource houtside hinsideBelow
      hinsideRow
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
  have hsupportS : PositiveInterfacePairSupportAt t o m
      externalThreshold width shell s vReplacement.length = eta.1.2 :=
    (orientedDominantPositiveInterfacePairSupportAt_prefix_invariant t o m
      externalThreshold width shell hp).trans hsupportReplacement
  rw [positiveInterfaceExternalPairRankAtom,
    orientedExternalAllCreationSupportTraceAtom_eq]
  refine ⟨hvalid, ⟨vReplacement.length, hcreationS.1⟩, ?_, ?_⟩
  · rw [htimeS]
    exact hcodeS
  · rw [htimeS]
    exact hsupportS

end

end Erdos1165.HLOZPositiveInterfacePairSupportActualDeltaAtom
