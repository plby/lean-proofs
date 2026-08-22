/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceSupportSelector
import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationStaticSupportTruncatedSharpTail
import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceAtomRecovery

/-!
# Prefix-correct recovery on the positive-interface support

The positive-interface product uses all retained dominoes whose endpoint
chain is thick and whose physical domino has not yet reached level `m`.
This file equips each exact `(trace, support)` atom with an honest broad
accepted-creation window.  The window truncates every away insertion total
strictly below the remaining distance to level `m`; consequently changing
away coordinates preserves the rank creation clock and the complete trace.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfaceAggregateRecovery

open HLOZPositiveInterfaceSupportSelector
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPathEvents
open LazyDecomposition PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingInsertedLocalTime
open TilingLazyDecomposition TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingOrientedPrefixedInsertionCode
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

abbrev PositiveInterfaceSupportAt
    (t : DominoTiling) (o : Orientation) (m externalThreshold : ℕ) :=
  orientedPositiveInterfaceSupportAt t o m externalThreshold

theorem positiveInterfaceSupportData
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ) :
    OrientedAllCreationSupportSelectorData t o m k
      (PositiveInterfaceSupportAt t o m externalThreshold) :=
  orientedPositiveInterfaceSupportSelectorData t o m k externalThreshold

abbrev PositiveInterfaceSupportedIndex
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ) :=
  OrientedAllCreationSupportedAtomIndex t o m k
    (PositiveInterfaceSupportAt t o m externalThreshold)

abbrev PositiveInterfaceFiber
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold) :=
  ConcreteFiber (positiveInterfaceSupportData t o m k externalThreshold) eta

/-- The physical optional terminal is independent of all insertion totals. -/
noncomputable def positiveInterfaceTerminal
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold) :
    Option Point :=
  prefixedTilingInsertionTerminal eta.1.1.external.initial t
    eta.1.1.external.start eta.1.1.external.retained (fun _ ↦ 0)
    eta.1.1.external.tail

theorem positiveInterfaceTerminal_eq_coordinates
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (q : Fin (eta.1.1.external.retainedCount + 1) → ℕ) :
    prefixedTilingInsertionTerminal eta.1.1.external.initial t
      eta.1.1.external.start eta.1.1.external.retained q
      eta.1.1.external.tail = positiveInterfaceTerminal eta := by
  exact prefixedTilingInsertionTerminal_eq_of_coordinates
    eta.1.1.external.initial t eta.1.1.external.start
    eta.1.1.external.retained q (fun _ ↦ 0) eta.1.1.external.tail rfl

/-- Every nonempty positive-rank atom has the oriented physical initial
prefix prescribed by its trace code. -/
theorem positiveInterfaceExternal_orientation
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) :
    match o with
    | .even => eta.1.1.external.initial.1 = []
    | .shifted => eta.1.1.external.initial.1.length = 1 := by
  rcases eta.2 with ⟨s, hs⟩
  have hcode : fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k s) s = eta.1.1.external :=
    congrArg OrientedAllCreationTraceCode.external hs.1.2.2
  cases o with
  | even =>
      have hinitial := congrArg
        (fun z : OrientedTilingTypedExternalWordCode t ↦ z.initial.1) hcode
      simpa [fixedOrientedTypedExternalWordCode, orientedInitialPrefix] using
        hinitial.symm
  | shifted =>
      have hcreation : ThresholdCreation s m k (creationTimeNat m k s) := by
        simpa [creationTimeNat, hs.1.2.1] using
          thresholdCreation_natFind hs.1.2.1
      have hnpos : 0 < creationTimeNat m k s := by
        by_contra hn
        have hnzero : creationTimeNat m k s = 0 := Nat.eq_zero_of_not_pos hn
        have hlocal := position_mem_thresholdSites_of_creation hk hcreation
        have hle := (mem_thresholdSites s _ m _).mp hlocal |>.2
        have hlocalZero : localTime s 0 (s 0) = 1 := by
          unfold localTime localTimePrefix pathPrefix
          simp
        rw [hnzero, hlocalZero] at hle
        omega
      have hinitial := congrArg
        (fun z : OrientedTilingTypedExternalWordCode t ↦ z.initial.1.length)
          hcode
      have hwordLength :
          (incrementPrefixList (creationTimeNat m k s)
            (stepsOfWalk s)).length = creationTimeNat m k s := by
        simp [incrementPrefixList]
      calc
        eta.1.1.external.initial.1.length =
            (fixedOrientedTypedExternalWordCode t .shifted
              (creationTimeNat m k s) s).initial.1.length := hinitial.symm
        _ = ((incrementPrefixList (creationTimeNat m k s)
              (stepsOfWalk s)).take 1).length := rfl
        _ = 1 := by rw [List.length_take, hwordLength]; omega

theorem positiveInterfaceFixedExternalCode_prefixedInsertion
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k)
    (q : Fin (eta.1.1.external.retainedCount + 1) → ℕ) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained q
        eta.1.1.external.tail.1
    fixedOrientedTypedExternalWordCode t o v.length
        (trajectory (extendPrefix (directionVectorOfList v))) =
      eta.1.1.external := by
  cases o with
  | even =>
      exact fixedOrientedTypedExternalWordCode_prefixedInsertion .even
        eta.1.1.external (positiveInterfaceExternal_orientation eta hm hk) q
  | shifted =>
      exact fixedOrientedTypedExternalWordCode_prefixedInsertion .shifted
        eta.1.1.external (positiveInterfaceExternal_orientation eta hm hk) q

/-- The support exclusion from the exact selected atom forces every away
domino of the represented path to stay strictly below level `m`. -/
theorem positiveInterfaceCanonical_strictAway
    {t : DominoTiling} {o : Orientation} {m k externalThreshold cap : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k
        (PositiveInterfaceSupportAt t o m externalThreshold)
        eta.1.1 eta.1.2)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1) :
    ∀ b : TilingExternalDomino t eta.1.1.external.start
        eta.1.1.external.retained,
      b.1 ∉ supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2 →
        prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
            eta.1.1.external.start eta.1.1.external.retained
            (positiveInterfaceTerminal eta) b +
          tilingDominoTotal t eta.1.1.external.start
            eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b < m := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hlt : v.length < orientedAllCreationCoordinateCutoff eta.1.1 cap :=
    prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1 cap q
  have hcreation : ThresholdCreation s m k v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff eta.1.1 cap)
        v.length _ hlt).mp haccepted
  have htime : creationTimeNat m k s = v.length :=
    creationTimeNat_eq_of_creation hcreation
  have hsupport : PositiveInterfaceSupportAt t o m externalThreshold
      s v.length = eta.1.2 := by
    rw [← htime]
    exact hcanonical.2
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath eta.1.1.external.initial.1
        eta.1.1.external.start
        (tilingInsertGapVector t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)))
        (positiveInterfaceTerminal eta) := by
    rw [← positiveInterfaceTerminal_eq_coordinates eta
      (fun j ↦ (q j : ℕ))]
    exact finitePathList_prefixedTilingInsertionPrefix
      eta.1.1.external.initial t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail rfl
  intro b hbAway
  have hbS : b.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.external.start
      eta.1.1.external.retained eta.1.2 b).1 hbAway
  have hbSupport : b.1 ∈ PositiveInterfaceSupportAt t o m
      externalThreshold s v.length := by
    rw [hsupport]
    exact hbS
  have hbNotThreshold : b.1 ∉
      (thresholdSites s v.length m).image (tilingBase t) := by
    unfold PositiveInterfaceSupportAt orientedPositiveInterfaceSupportAt
      orientedPositiveInterfaceCodeSupport at hbSupport
    exact (Finset.mem_filter.mp hbSupport).2.2
  have hbaseLt : localTime s v.length b.1 < m := by
    by_contra hnot
    apply hbNotThreshold
    rw [Finset.mem_image]
    exact ⟨b.1, (mem_thresholdSites_iff s v.length m b.1 (by omega)).2
      (Nat.le_of_not_gt hnot),
      tilingExternalDomino_isBase t eta.1.1.external.start
        eta.1.1.external.retained b⟩
  have hpartnerLt : localTime s v.length (tilingPartner t b.1) < m := by
    by_contra hnot
    apply hbNotThreshold
    rw [Finset.mem_image]
    refine ⟨tilingPartner t b.1,
      (mem_thresholdSites_iff s v.length m (tilingPartner t b.1)
        (by omega)).2 (Nat.le_of_not_gt hnot), ?_⟩
    rw [tilingBase_partner]
    exact tilingExternalDomino_isBase t eta.1.1.external.start
      eta.1.1.external.retained b
  have hbase : localTime s v.length b.1 =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (positiveInterfaceTerminal eta) b.1 +
        tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        (positiveInterfaceTerminal eta) b b.1]
    exact tilingExternalDomino_isBase t eta.1.1.external.start
      eta.1.1.external.retained b
  have hpartner : localTime s v.length (tilingPartner t b.1) =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (positiveInterfaceTerminal eta) (tilingPartner t b.1) +
        tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        (positiveInterfaceTerminal eta) b (tilingPartner t b.1)]
    exact tilingPartner_ofExternalDomino_has_base t eta.1.1.external.start
      eta.1.1.external.retained b
  unfold prefixedTilingFixedBoundaryDominoMax
  rw [show max
      (prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (positiveInterfaceTerminal eta) b.1)
      (prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (positiveInterfaceTerminal eta) (tilingPartner t b.1)) +
      tilingDominoTotal t eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) b =
      max
        (prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (positiveInterfaceTerminal eta) b.1 +
          tilingDominoTotal t eta.1.1.external.start
            eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b)
        (prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (positiveInterfaceTerminal eta) (tilingPartner t b.1) +
          tilingDominoTotal t eta.1.1.external.start
            eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b) by omega,
    max_lt_iff]
  exact ⟨hbase ▸ hbaseLt, hpartner ▸ hpartnerLt⟩

/-- The safe broad window leaves every away domino strictly below level
`m`, after accounting for its fixed initial/retained/terminal boundary
visits. -/
noncomputable def positiveInterfaceBaseWindow
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)) : Finset ℕ :=
  Finset.range (m - prefixedTilingFixedBoundaryDominoMax
    eta.1.1.external.initial.1 eta.1.1.external.start
    eta.1.1.external.retained (positiveInterfaceTerminal eta) b.1)

/-- Honest prefix-correct recovery for the positive-interface aggregate
screen.  It has no chosen coordinate and works for empty support. -/
noncomputable def positiveInterfaceStaticSupportRecoveryCertificate
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) :
    StaticSupportRecoveryCertificate
      (positiveInterfaceSupportData t o m k externalThreshold) eta where
  baseWindow cap := positiveInterfaceBaseWindow eta cap
  recover cap q hselected hscreen := by
    classical
    let D := supportComplementDistinguished t eta.1.1.external.start
      eta.1.1.external.retained eta.1.2
    change orientedAllCreationSelected o m k
      (PositiveInterfaceSupportAt t o m externalThreshold)
      eta.1.2 eta.1.1 ((PositiveInterfaceFiber eta).coordinateCap cap)
      ((splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained D q).1) at hselected
    rcases hselected with ⟨a', hselected⟩
    let q' : TilingCappedCoordinates eta.1.1.external.retainedCount
        ((PositiveInterfaceFiber eta).coordinateCap cap) :=
      (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained D).symm
          ((splitTilingCoordinatesEquiv t eta.1.1.external.start
            eta.1.1.external.retained D q).1, a')
    change orientedAllCreationStoppedAtomPredicate o m k
        (PositiveInterfaceSupportAt t o m externalThreshold)
          eta.1.2 eta.1.1 ((PositiveInterfaceFiber eta).coordinateCap cap) q' ∧
      PrefixedTilingStoppingAccepted
        ((PositiveInterfaceFiber eta).stoppingTime cap)
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
        eta.1.1.external.tail.1 at hselected
    rcases hselected with ⟨hpred', haccepted'⟩
    have hsplit' := (splitTilingCoordinatesEquiv t eta.1.1.external.start
      eta.1.1.external.retained D).apply_symm_apply
        ((splitTilingCoordinatesEquiv t eta.1.1.external.start
          eta.1.1.external.retained D q).1, a')
    have hdist : (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained D q).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained D q').1 := by
      exact (congrArg Prod.fst hsplit').symm
    have hcanonical' := canonical_mem_supportAtom_of_predicate_accepted
      ((PositiveInterfaceFiber eta).coordinateCap cap) q' hpred' haccepted'
    rcases hscreen with ⟨ell, hell, htotal⟩
    change ∀ b : TilingAwayDomino t eta.1.1.external.start
        eta.1.1.external.retained D,
      tilingAwayTotal t eta.1.1.external.start eta.1.1.external.retained D
        ((splitTilingCoordinatesEquiv t eta.1.1.external.start
          eta.1.1.external.retained D q).2) b = ell b at htotal
    have hbelow : ∀ b : TilingExternalDomino t eta.1.1.external.start
        eta.1.1.external.retained, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (positiveInterfaceTerminal eta) b +
        tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b < m := by
      intro b hb
      let ba : TilingAwayDomino t eta.1.1.external.start
          eta.1.1.external.retained D := ⟨b, hb⟩
      have hwindow := hell ba
      change (ell ba : ℕ) ∈ Finset.range
        (m - prefixedTilingFixedBoundaryDominoMax
          eta.1.1.external.initial.1 eta.1.1.external.start
          eta.1.1.external.retained (positiveInterfaceTerminal eta) b) at hwindow
      rw [Finset.mem_range] at hwindow
      rw [← tilingAwayTotal_split_eq_dominoTotal t
        eta.1.1.external.start eta.1.1.external.retained D q ba,
        htotal ba]
      omega
    have hbelow' : ∀ b : TilingExternalDomino t eta.1.1.external.start
        eta.1.1.external.retained, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (positiveInterfaceTerminal eta) b +
        tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q' j : ℕ)) b < m := by
      exact positiveInterfaceCanonical_strictAway eta hm q' hcanonical'
        haccepted'
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    let s' := trajectory (extendPrefix (directionVectorOfList v'))
    have hstart : trajectory (extendPrefix (directionVectorOfList
        eta.1.1.external.initial.1)) eta.1.1.external.initial.1.length =
        eta.1.1.external.start := rfl
    have hpath : finitePathList (pathPrefix s v.length) =
        prefixedTilingPrefixPointPath eta.1.1.external.initial.1
          eta.1.1.external.start
          (tilingInsertGapVector t eta.1.1.external.start
            eta.1.1.external.retained (fun j ↦ (q j : ℕ)))
          (positiveInterfaceTerminal eta) := by
      rw [← positiveInterfaceTerminal_eq_coordinates eta
        (fun j ↦ (q j : ℕ))]
      exact finitePathList_prefixedTilingInsertionPrefix
        eta.1.1.external.initial t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        eta.1.1.external.tail hstart
    have hpath' : finitePathList (pathPrefix s' v'.length) =
        prefixedTilingPrefixPointPath eta.1.1.external.initial.1
          eta.1.1.external.start
          (tilingInsertGapVector t eta.1.1.external.start
            eta.1.1.external.retained (fun j ↦ (q' j : ℕ)))
          (positiveInterfaceTerminal eta) := by
      rw [← positiveInterfaceTerminal_eq_coordinates eta
        (fun j ↦ (q' j : ℕ))]
      exact finitePathList_prefixedTilingInsertionPrefix
        eta.1.1.external.initial t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
        eta.1.1.external.tail hstart
    have hlt : v.length < orientedAllCreationCoordinateCutoff eta.1.1
        ((PositiveInterfaceFiber eta).coordinateCap cap) :=
      prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1
        ((PositiveInterfaceFiber eta).coordinateCap cap) q
    have hlt' : v'.length < orientedAllCreationCoordinateCutoff eta.1.1
        ((PositiveInterfaceFiber eta).coordinateCap cap) :=
      prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1
        ((PositiveInterfaceFiber eta).coordinateCap cap) q'
    have hcreation' : ThresholdCreation s' m k v'.length := by
      apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m k
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((PositiveInterfaceFiber eta).coordinateCap cap)) v'.length _
          hlt').mp
      exact haccepted'
    have hterminalHigh' : m ≤ localTime s' v'.length (s' v'.length) :=
      (mem_thresholdSites s' v'.length m (s' v'.length)).mp
        (position_mem_thresholdSites_of_creation hk hcreation') |>.2
    have hend : s v.length = s' v'.length :=
      prefixedTilingInsertionEndpoint_eq_of_coordinates
        eta.1.1.external.initial t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail hstart
    have hendpointLocal : localTime s v.length (s v.length) =
        localTime s' v'.length (s' v'.length) := by
      rw [localTime_eq_listLocalTime, localTime_eq_listLocalTime,
        hpath, hpath', hend]
      apply prefixedTilingPrefixLocalTime_eq_of_ge_level
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained (positiveInterfaceTerminal eta) m D q q'
        hdist hbelow hbelow' (s' v'.length)
      refine Or.inr ?_
      rw [← hpath', ← localTime_eq_listLocalTime]
      exact hterminalHigh'
    have hpos' : 0 < v'.length := by
      by_contra hn
      have hnzero : v'.length = 0 := Nat.eq_zero_of_not_pos hn
      have hlocalZero : localTime s' 0 (s' 0) = 1 := by
        unfold localTime localTimePrefix pathPrefix
        simp
      rw [hnzero, hlocalZero] at hterminalHigh'
      omega
    have hterminalHigh : m ≤ localTime s v.length (s v.length) := by
      rw [hendpointLocal]
      exact hterminalHigh'
    have hpos : 0 < v.length := by
      by_contra hn
      have hnzero : v.length = 0 := Nat.eq_zero_of_not_pos hn
      have hlocalZero : localTime s 0 (s 0) = 1 := by
        unfold localTime localTimePrefix pathPrefix
        simp
      rw [hnzero, hlocalZero] at hterminalHigh
      omega
    have hbelowQ : ∀ b : TilingExternalDomino t
        eta.1.1.external.start eta.1.1.external.retained, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (prefixedTilingInsertionTerminal eta.1.1.external.initial t
            eta.1.1.external.start eta.1.1.external.retained
            (fun j ↦ (q j : ℕ)) eta.1.1.external.tail) b +
        tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b < m := by
      simpa only [positiveInterfaceTerminal_eq_coordinates eta
        (fun j ↦ (q j : ℕ))] using hbelow
    have hbelowQ' : ∀ b : TilingExternalDomino t
        eta.1.1.external.start eta.1.1.external.retained, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (prefixedTilingInsertionTerminal eta.1.1.external.initial t
            eta.1.1.external.start eta.1.1.external.retained
            (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail) b +
        tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q' j : ℕ)) b < m := by
      simpa only [positiveInterfaceTerminal_eq_coordinates eta
        (fun j ↦ (q' j : ℕ))] using hbelow'
    have haccepted : PrefixedTilingStoppingAccepted
        ((PositiveInterfaceFiber eta).stoppingTime cap)
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        eta.1.1.external.tail.1 := by
      apply (prefixedTilingStoppingAccepted_iff_of_strictAway_of_endpointLocal
        eta.1.1.external.initial t eta.1.1.external.start m k
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((PositiveInterfaceFiber eta).coordinateCap cap))
        (by omega) hk eta.1.1.external.retained eta.1.1.external.tail
        D q q' hstart hdist hbelowQ hbelowQ' hpos hpos' hlt hlt'
        hendpointLocal).mpr
      exact haccepted'
    have hsites : thresholdSites s v.length m =
        thresholdSites s' v'.length m := by
      exact thresholdSites_prefixedTilingInsertionPrefix_eq_of_distinguished_eq
        eta.1.1.external.initial t eta.1.1.external.start
        eta.1.1.external.retained eta.1.1.external.tail m (by omega)
        D q q' hstart hdist hbelowQ hbelowQ'
    have hfavorite : favoriteSites s v.length =
        favoriteSites s' v'.length :=
      favoriteSites_prefixedInsertion_eq_of_distinguished_eq_of_strictAway
        eta.1.1.external.initial t eta.1.1.external.start m k
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((PositiveInterfaceFiber eta).coordinateCap cap)) hk
        eta.1.1.external.retained eta.1.1.external.tail D q q' hstart
        hdist hbelowQ hbelowQ' haccepted haccepted' hlt hlt'
    have hcreation : ThresholdCreation s m k v.length :=
      (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m k
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((PositiveInterfaceFiber eta).coordinateCap cap)) v.length _
          hlt).mp haccepted
    have htime' : creationTimeNat m k s' = v'.length :=
      creationTimeNat_eq_of_creation hcreation'
    have htrace' : fixedOrientedAllCreationTraceCode t o v'.length s' =
        eta.1.1 := by
      rw [← htime']
      exact hcanonical'.1.2.2
    have hexternal : fixedOrientedTypedExternalWordCode t o v.length s =
        eta.1.1.external :=
      positiveInterfaceFixedExternalCode_prefixedInsertion eta hm hk
        (fun j ↦ (q j : ℕ))
    have hexternal' : fixedOrientedTypedExternalWordCode t o v'.length s' =
        eta.1.1.external :=
      congrArg OrientedAllCreationTraceCode.external htrace'
    have hsupport' : PositiveInterfaceSupportAt t o m externalThreshold
        s' v'.length = eta.1.2 := by
      rw [← htime']
      exact hcanonical'.2
    have hsupport : PositiveInterfaceSupportAt t o m externalThreshold
        s v.length = eta.1.2 := by
      calc
        PositiveInterfaceSupportAt t o m externalThreshold s v.length =
            PositiveInterfaceSupportAt t o m externalThreshold s' v'.length := by
          unfold PositiveInterfaceSupportAt
            orientedPositiveInterfaceSupportAt
          rw [hexternal, hexternal', hsites]
        _ = eta.1.2 := hsupport'
    have htrace : fixedOrientedAllCreationTraceCode t o v.length s =
        eta.1.1 := by
      rw [OrientedAllCreationTraceCode.mk.injEq]
      refine ⟨hexternal, ?_⟩
      have hfavorite' := congrArg OrientedAllCreationTraceCode.favorite htrace'
      change ((favoriteSites s v.length,
          (favoriteSites s v.length).image (tilingBase t)),
        ((fixedOrientedTypedExternalWordCode t o v.length s).start,
          s v.length)) = eta.1.1.favorite
      calc
        ((favoriteSites s v.length,
            (favoriteSites s v.length).image (tilingBase t)),
          ((fixedOrientedTypedExternalWordCode t o v.length s).start,
            s v.length)) =
          ((favoriteSites s' v'.length,
              (favoriteSites s' v'.length).image (tilingBase t)),
            ((fixedOrientedTypedExternalWordCode t o v'.length s').start,
              s' v'.length)) := by
            rw [hfavorite, hend, hexternal, hexternal']
        _ = eta.1.1.favorite := hfavorite'
    have hcanonical : s ∈ orientedAllCreationSupportTraceAtom t o m k
        (PositiveInterfaceSupportAt t o m externalThreshold)
        eta.1.1 eta.1.2 := by
      refine ⟨⟨trajectory_mem_validStepWalk _, ⟨v.length, hcreation.1⟩,
        ?_⟩, ?_⟩
      · rw [creationTimeNat_eq_of_creation hcreation]
        exact htrace
      · change PositiveInterfaceSupportAt t o m externalThreshold s
          (creationTimeNat m k s) = eta.1.2
        rw [creationTimeNat_eq_of_creation hcreation]
        exact hsupport
    refine ⟨?_, haccepted⟩
    exact atomPredicate_of_canonical_mem_accepted
      (positiveInterfaceSupportData t o m k externalThreshold)
      ((PositiveInterfaceFiber eta).coordinateCap cap) q hcanonical haccepted

end

end Erdos1165.HLOZPositiveInterfaceAggregateRecovery
