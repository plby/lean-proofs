/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroDeltaReplacementFactorization

/-!
# Soundness of one honest actual-delta replacement fibre

The fixed-delta predicate is not merely accepted at the raised clock.  Its
physical prefixed reconstruction belongs to the corresponding literal
external-word/static-support replacement atom.  In particular the raised
rank, `Dtilde`, restricted-Theta screen, exact two-window cardinalities, and
static support are all recovered from the coordinate screen.
-/

namespace Erdos1165.TilingShellZeroDeltaReplacementSound

open FiniteDominoProductLaw HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroExternalWindow
open HLOZShellZeroReplacementWindows LazyDecomposition
open PathInsertion PreStoppingFiber SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingLazyDecomposition TilingOrientedShellZeroSourcePartition
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroActualDeltaPartition
open TilingShellZeroActualDeltaReplacementAtomRecovery
open TilingShellZeroDeltaReplacementFactorization
open TilingShellZeroEndpointIncrementScreen
open TilingShellZeroExternalStaticSupportData
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroFactoredCapScreen
open TilingShellZeroSourcePartition TilingShellZeroSourceScreenForward
open TilingShellZeroStaticReplacementSupportRecovery
open TilingShellZeroSupportedSourceStaticFacts
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The literal fixed-delta predicate reconstructs the complete honest
actual-delta replacement atom. -/
theorem replacement_sound
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total cap central : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (hm : 1 < m) (hk : 0 < k) (hlow : low < m)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh)
    (hcentral : central < total)
    (delta : ReplacementEndpointIncrement total central)
    (qReplacement : TilingCappedCoordinates eta.1.1.retainedCount
      (coordinateCap eta.1.1 m cap))
    (hq : replacementPredicate eta cap central delta qReplacement) :
    canonicalPath eta.1.1 (fun j ↦ (qReplacement j : ℕ)) ∈
      orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
        t o m k (shellWidth48 m) low externalLow externalHigh total central
          delta eta.1.1 eta.1.2 := by
  classical
  rcases hq.1 with ⟨aSource, hsource⟩
  let qSource := (splitTilingCoordinatesEquiv t eta.1.1.start
    eta.1.1.retained (staticD eta.1.1 eta.1.2)).symm
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2) qReplacement).1, aSource)
  have hsourceForward := source_forward eta hm hk hexternal qSource hsource
  rcases hsourceForward.2 with ⟨ellSource, hellSource, htotalSourceAway⟩
  rcases hq.2 with ⟨ellReplacement, hellReplacement,
    htotalReplacementAway⟩
  have hdist : (splitTilingCoordinatesEquiv t eta.1.1.start
      eta.1.1.retained (staticD eta.1.1 eta.1.2) qSource).1 =
    (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (staticD eta.1.1 eta.1.2) qReplacement).1 := by
    simp only [qSource, Equiv.apply_symm_apply]
  have hterminal : prefixedTilingInsertionTerminal eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
        eta.1.1.tail = staticTerminal eta.1.1 := by
    apply prefixedTilingInsertionTerminal_eq_of_coordinates
      eta.1.1.initial t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qSource j : ℕ)) (fun _ ↦ 0) eta.1.1.tail rfl
  have hbase : ∀ b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (staticD eta.1.1 eta.1.2),
    prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained
        (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
          eta.1.1.retained (fun j ↦ (qSource j : ℕ)) eta.1.1.tail) b.1.1 =
      Fintype.card (TilingCoordinatesAt t eta.1.1.start
        eta.1.1.retained b.1) := by
    intro b
    exact boundaryLocalTime_eq_coordinateCard eta hm hk
      (fun j ↦ (qSource j : ℕ)) b.1
      ((away_mem_support_iff t eta.1.1.start eta.1.1.retained
        eta.1.2 b.1).1 b.2)
  have hdominance := boundary_dominance_of_source eta hm hk qSource
    hsource.1 hsource.2
  have htranslate : ∀ b : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained (staticD eta.1.1 eta.1.2),
      Fintype.card (TilingCoordinatesAt t eta.1.1.start
        eta.1.1.retained b.1) ≤ m - shellWidth48 m + 1 := by
    intro b
    exact ((coordinateSupportData t o m k (shellWidth48 m) low externalLow
      externalHigh total cap eta hm).toWindowData hexternal).translate b
  have hsourceCoordinate : ∀ b,
      tilingShellZeroSourceCoordinate
        (cap := coordinateCap eta.1.1 m cap) (m := m)
        (w := shellWidth48 m) t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2) (upper eta.1.1 eta.1.2 m)
        b (ellSource b) := by
    intro b
    exact hellSource b
  have htotalSource : ∀ b,
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qSource j : ℕ)) b.1 = (ellSource b : ℕ) := by
    intro b
    calc
      _ = tilingAwayTotal t eta.1.1.start eta.1.1.retained
          (staticD eta.1.1 eta.1.2)
          ((splitTilingCoordinatesEquiv t eta.1.1.start
            eta.1.1.retained (staticD eta.1.1 eta.1.2) qSource).2) b :=
        (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
          eta.1.1.retained (staticD eta.1.1 eta.1.2) qSource b).symm
      _ = _ := htotalSourceAway b
  have htotalReplacement : ∀ b,
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qReplacement j : ℕ)) b.1 = (ellReplacement b : ℕ) := by
    intro b
    calc
      _ = tilingAwayTotal t eta.1.1.start eta.1.1.retained
          (staticD eta.1.1 eta.1.2)
          ((splitTilingCoordinatesEquiv t eta.1.1.start
            eta.1.1.retained (staticD eta.1.1 eta.1.2) qReplacement).2) b :=
        (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
          eta.1.1.retained (staticD eta.1.1 eta.1.2) qReplacement b).symm
      _ = _ := htotalReplacementAway b
  have hsourceD :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
          eta.1.1.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingDEtaAt t m k (shellWidth48 m) low s v.length := by
    have hevent := hsource.1.1.1.1
    have hD := hevent.2.1
    have htime := source_creation_time_eq eta.1.1 qSource hsource.2
    rw [htime] at hD
    exact hD
  have hsourceSupport :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
          eta.1.1.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length =
          eta.1.2 := by
    have hsupp := hsource.1.2
    change sourceStaticSupport t o m k (shellWidth48 m)
      (canonicalPath eta.1.1 (fun j ↦ (qSource j : ℕ))) = eta.1.2 at hsupp
    have htime := source_creation_time_eq eta.1.1 qSource hsource.2
    rw [sourceStaticSupport, htime] at hsupp
    exact hsupp
  have hcompat : ∀ b ∈ eta.1.2, OrientationCompatible o b :=
    orientationCompatible_of_mem_staticSupport eta
  have hcard : eta.1.2.card = total := card_staticSupport eta
  have hsourcePos : 0 < (prefixedTilingInsertionPrefixList
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qSource j : ℕ)) eta.1.1.tail.1).length := by
    rw [← source_creation_time_eq eta.1.1 qSource hsource.2]
    exact creationTimeNat_pos_of_mem_sourceStaticSupportAtom hm hsource.1
  have hacceptedReplacement := replacement_accepted eta hm hk hlow harithmetic
    hexternal hcentral delta qReplacement hq
  let vReplacement := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (qReplacement j : ℕ))
      eta.1.1.tail.1
  let sReplacement := trajectory
    (extendPrefix (directionVectorOfList vReplacement))
  have hcreationReplacement : ThresholdCreation sReplacement m
      (k + (delta : ℕ)) vReplacement.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1 (coordinateCap eta.1.1 m cap))
      vReplacement.length (extendPrefix (directionVectorOfList vReplacement))
      (insertion_lt_cutoff eta.1.1 m cap qReplacement)).mp
    exact hacceptedReplacement
  have hreplacementPos : 0 < vReplacement.length := by
    by_contra hn
    have hzero : vReplacement.length = 0 := Nat.eq_zero_of_not_pos hn
    have hsite := position_mem_thresholdSites_of_creation (by omega)
      hcreationReplacement
    have hlevel := (mem_thresholdSites sReplacement _ m _).mp hsite |>.2
    have hlocal : localTime sReplacement 0 (sReplacement 0) = 1 := by
      simp [localTime, localTimePrefix, pathPrefix]
    rw [hzero, hlocal] at hlevel
    omega
  have hcodeReplacement : fixedOrientedTypedExternalWordCode t o
      vReplacement.length sReplacement = eta.1.1 := by
    exact fixedCode_prefixedInsertion eta hm hk
      (fun j ↦ (qReplacement j : ℕ))
  have hexternalWindow : ∀ b ∈ eta.1.2,
      externalLow ≤
          HLOZSourceOrientedExternalLocalTime.tilingSourceExternalBaseLocalTime
            t o sReplacement vReplacement.length b ∧
        HLOZSourceOrientedExternalLocalTime.tilingSourceExternalBaseLocalTime
          t o sReplacement vReplacement.length b < externalHigh := by
    apply sourceExternalWindow_of_fixedCode
      (s := sReplacement) (z := eta.1.1)
      (trajectory_mem_validStepWalk _) hreplacementPos hcodeReplacement
      (sourceStaticSupport_subset_externalDominoBases eta) hcompat
    intro b hb
    let baway : TilingAwayDomino t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2) :=
      ⟨b, by
        simp only [staticD, supportComplementDistinguished,
          Finset.mem_sdiff, b.2, true_and, not_not]
        exact hb⟩
    exact (coordinateSupportData t o m k (shellWidth48 m) low externalLow
      externalHigh total cap eta hm).externalWindow baway
  have hresult := prefixedReplacement_mem_actualDeltaStaticSupportAtom
    eta.1.1.initial t o eta.1.1.start eta.1.1.retained eta.1.1.tail
    eta.1.1 eta.1.2 (sourceStaticSupport_subset_externalDominoBases eta)
    (upper eta.1.1 eta.1.2 m) central delta
    (externalCoordinateCutoff eta.1.1 (coordinateCap eta.1.1 m cap))
    hm hk hlow qSource qReplacement ellSource ellReplacement rfl hdist
    (by simpa only [staticD, supportComplementDistinguished] using hbase)
    (by simpa only [staticD, supportComplementDistinguished] using hdominance)
    (by simpa only [staticD, supportComplementDistinguished] using htranslate)
    (by simpa only [staticD, supportComplementDistinguished] using
      hsourceCoordinate)
    (by simpa only [replacementScreen, staticD,
      supportComplementDistinguished, hterminal] using hellReplacement)
    (by simpa only [staticD, supportComplementDistinguished] using htotalSource)
    (by simpa only [staticD, supportComplementDistinguished] using
      htotalReplacement)
    hsourceD hsourceSupport hcompat hcard hexternalWindow hsource.2 hsourcePos
    hreplacementPos (insertion_lt_cutoff eta.1.1 m cap qSource)
    (insertion_lt_cutoff eta.1.1 m cap qReplacement) hcodeReplacement
  simpa only [canonicalPath] using hresult

end

end Erdos1165.TilingShellZeroDeltaReplacementSound
