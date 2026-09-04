/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWindowTailObservableCap

/-!
# Exact observable atom for a positive-interface source cap

The physical source screen already records both prefix safety and the full
adjacent-pair support.  Consequently its canonical stopped paths remain in
the exact external-word/support atom at the original creation rank, without
assuming the later window-ratio arithmetic certificate.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZPositiveInterfacePairSourceCapAtom

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZPathEvents
open HLOZPositiveInterfaceExternalPairCoordinateRecovery
open HLOZPositiveInterfacePairActualDeltaCapBound
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairSupportActualDeltaAtom
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairSupportPreservingBound
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfacePairWeightedScreen
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZSourceOrientedThetaAcceptedCreationPath
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
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

/-- Every source-screened cap lies in its exact external-word/support atom
at the original creation rank.  Unlike the replacement analogue, this uses
the source screen's own prefix-safe base window and needs no ratio
certificate. -/
theorem positiveInterfaceExternalPairSourceCap_subset_pairRankAtom
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m) (hk : 0 < k) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ) :
    positiveInterfaceExternalPairSourceCap eta cap threshold bound ⊆
      positiveInterfaceExternalPairRankAtom t o m k externalThreshold width
        shell 0 eta := by
  classical
  let : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)
  intro s hs
  rcases hs with ⟨hvalid, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨qAccepted, hq⟩
  let data := PositiveInterfaceExternalPairFiber eta
  let qReplacement := qAccepted.1
  have hpred := qAccepted.2.1
  have hacceptedReplacement := qAccepted.2.2
  change positiveInterfaceExternalPairSourcePredicate eta cap threshold bound
      qReplacement at hpred
  rcases hpred with
    ⟨hselected, ellReplacement, hsourceScreen,
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
  have hreplacementScreen :
      positiveInterfaceExternalPairReplacementScreen eta cap
        ellReplacement := by
    intro c
    have hc : c ∈ pairSupport
        (positiveInterfaceExternalPairUpper eta cap)
        (positiveInterfaceExternalPairLower eta cap) ellReplacement := by
      rw [hsourceScreen.2.2]
      exact Finset.mem_univ c
    simpa only [pairSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      using hc
  have hinsideBelow : ∀ b ∈ eta.1.2,
      localTime sReplacement vReplacement.length b < m ∧
        localTime sReplacement vReplacement.length (tilingPartner t b) < m := by
    intro b hbS
    let c := supportAwayChosen t eta.1.1.start eta.1.1.retained eta.1.2
      data.support_represented b hbS
    have hcBase : c.1.1 = b := supportAwayChosen_base t eta.1.1.start
      eta.1.1.retained eta.1.2 data.support_represented b hbS
    have hcSafe : (ellReplacement c : ℕ) ∈
        positiveInterfaceExternalPairBaseWindow eta cap c :=
      hsourceScreen.1 c
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
  have hcreationReplacement : ThresholdCreation sReplacement m k
      vReplacement.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m k
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
  have hcreationS : ThresholdCreation s m k vReplacement.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp
      (Nat.le_refl vReplacement.length)).mpr hcreationReplacement
  have htimeS : creationTimeNat m k s = vReplacement.length :=
    creationTimeNat_eq_of_creation hcreationS
  have hcodeS : fixedOrientedTypedExternalWordCode t o vReplacement.length s =
      eta.1.1 :=
    (fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp).trans
      hcodeReplacement
  have hsupportS : PositiveInterfacePairSupportAt t o m
      externalThreshold width shell s vReplacement.length = eta.1.2 :=
    (HLOZDominantPositiveInterfaceSupportSelector.orientedDominantPositiveInterfacePairSupportAt_prefix_invariant
      t o m
      externalThreshold width shell hp).trans hsupportReplacement
  rw [positiveInterfaceExternalPairRankAtom,
    orientedExternalAllCreationSupportTraceAtom_eq]
  simp only [Nat.add_zero]
  refine ⟨hvalid, ⟨vReplacement.length, hcreationS.1⟩, ?_, ?_⟩
  · rw [htimeS]
    exact hcodeS
  · rw [htimeS]
    exact hsupportS

end

end Erdos1165.HLOZPositiveInterfacePairSourceCapAtom
