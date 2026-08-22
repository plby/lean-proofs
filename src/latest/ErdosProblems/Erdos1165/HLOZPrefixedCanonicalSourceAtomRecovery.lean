/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceLowRecovery
import ErdosProblems.Erdos1165.TilingOrientedPrefixedInsertionCode

/-!
# Exact-atom recovery for the canonical Proposition 4.9 source

This file discharges the deterministic reverse direction of the honest
conditional product.  It is separate from the negative-binomial window
ratio and from the future escape estimate.
-/

open Set

namespace Erdos1165.HLOZPrefixedCanonicalSourceAtomRecovery

open FiniteDominoProductLaw
open HLOZCanonicalDominantCandidateWindows HLOZPathEvents
open HLOZPrefixedAllCreationCanonicalRefinement
open HLOZPrefixedAllCreationCanonicalDominantWindows
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedTilingConditionalCoordinateReconstruction
open HLOZProposition48Candidates HLOZShellZeroReplacementWindows
open HLOZThetaSourceBalance
open LazyDecomposition PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingOrientedPrefixedInsertionCode
open TilingShellZeroSourcePartition
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroAllCreationTraceBridge
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The eventually-constant path represented by accepted coordinates lies
in the exact atom named by the concrete fibre predicate. -/
theorem canonical_mem_supportAtom_of_predicate_accepted
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {S : Finset Point} {z : OrientedAllCreationTraceCode t}
    (cap : ℕ) (q : TilingCappedCoordinates z.external.retainedCount cap)
    (hpred : orientedAllCreationStoppedAtomPredicate
      o m k supportAt S z cap q)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff z cap))
      z.external.initial.1 t z.external.start z.external.retained
      (fun j ↦ (q j : ℕ)) z.external.tail.1) :
    trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList z.external.initial.1 t
        z.external.start z.external.retained (fun j ↦ (q j : ℕ))
        z.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k supportAt z S := by
  apply hpred
  unfold prefixedTilingStoppedInsertionAtom
  refine ⟨haccepted, ?_⟩
  unfold incrementPrefixList
  rw [stepPrefix_extendPrefix, ofFn_directionVectorOfList]

/-- Conversely, exact membership of the canonical represented path and
acceptance of its creation clock make the whole stopped cylinder sound. -/
theorem atomPredicate_of_canonical_mem_accepted
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData
      t o m k supportAt)
    {S : Finset Point} {z : OrientedAllCreationTraceCode t}
    (cap : ℕ) (q : TilingCappedCoordinates z.external.retainedCount cap)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList z.external.initial.1 t
        z.external.start z.external.retained (fun j ↦ (q j : ℕ))
        z.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k supportAt z S)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff z cap))
      z.external.initial.1 t z.external.start z.external.retained
      (fun j ↦ (q j : ℕ)) z.external.tail.1) :
    orientedAllCreationStoppedAtomPredicate
      o m k supportAt S z cap q := by
  let v := prefixedTilingInsertionPrefixList z.external.initial.1 t
    z.external.start z.external.retained (fun j ↦ (q j : ℕ))
    z.external.tail.1
  let canonical := trajectory (extendPrefix (directionVectorOfList v))
  have hlt : v.length < orientedAllCreationCoordinateCutoff z cap := by
    exact prefixedInsertion_lt_orientedAllCreationCoordinateCutoff z cap q
  have hcreation : ThresholdCreation canonical m k v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff z cap) v.length _ hlt).mp
        haccepted
  intro omega homega
  let somega := trajectory omega
  have hp : pathPrefix somega v.length = pathPrefix canonical v.length := by
    simpa only [somega, canonical, v] using
      (pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
        z.external.initial.1 z.external.start z.external.retained
        (fun j ↦ (q j : ℕ)) z.external.tail.1 omega homega)
  have hcreationOmega : ThresholdCreation somega m k v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp (Nat.le_refl v.length)).mpr
      hcreation
  have htime : creationTimeNat m k somega = v.length :=
    creationTimeNat_eq_of_creation hcreationOmega
  have hcanonicalTime : creationTimeNat m k canonical = v.length :=
    creationTimeNat_eq_of_creation hcreation
  refine ⟨⟨trajectory_mem_validStepWalk omega,
    ⟨v.length, hcreationOmega.1⟩, ?_⟩, ?_⟩
  · change fixedOrientedAllCreationTraceCode t o
      (creationTimeNat m k somega) somega = z
    rw [htime]
    have hcode : fixedOrientedAllCreationTraceCode t o v.length canonical = z := by
      rw [← hcanonicalTime]
      exact hcanonical.1.2.2
    exact (fixedOrientedAllCreationTraceCode_eq_of_pathPrefix_eq t o hp).trans
      hcode
  · change supportAt somega (creationTimeNat m k somega) = S
    rw [htime]
    have hsupport : supportAt canonical v.length = S := by
      rw [← hcanonicalTime]
      exact hcanonical.2
    exact (supportData.prefix_invariant hp).trans hsupport

/-- The chosen source point is the fixed base-dominant endpoint.  This is
the inequality form consumed by the exact broad/narrow window rewrites. -/
theorem sourceChosen_fixedBoundary_partner_le_base
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k) (candidate : Point)
    (hcandidate : candidate ∈ eta.1.2) :
    prefixedTilingFixedBoundaryLocalTime
          ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (sourceTerminal eta)
          (tilingPartner t (sourceChosen cap eta candidate hcandidate).1.1) ≤
      prefixedTilingFixedBoundaryLocalTime
          ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (sourceTerminal eta)
          (sourceChosen cap eta candidate hcandidate).1.1 := by
  have hdominant := sourceChosen_fixedDominant cap eta candidate hcandidate
  unfold prefixedTilingFixedDominantEndpoint at hdominant
  split at hdominant
  next hle => exact hle
  next hnot =>
    exfalso
    apply tilingPartner_ne t candidate
    rw [← sourceChosen_base cap eta candidate hcandidate]
    exact hdominant

/-- A nonempty positive-level source atom has the physical initial prefix
prescribed by its orientation. -/
theorem sourceExternal_orientation
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (hm : 1 < m) (hk : 0 < k) :
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

/-- Every insertion vector in a source atom's retained carrier reconstructs
its exact oriented external word. -/
theorem sourceFixedExternalCode_prefixedInsertion
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (hm : 1 < m) (hk : 0 < k)
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
        eta.1.1.external (sourceExternal_orientation eta hm hk) q
  | shifted =>
      exact fixedOrientedTypedExternalWordCode_prefixedInsertion .shifted
        eta.1.1.external (sourceExternal_orientation eta hm hk) q

/-- Every away domino in a canonical exact source atom lies in `V₂(I₁)`, so
both physical endpoint local times are strictly below the creation level. -/
theorem sourceCanonical_strictAway
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
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
            (sourceTerminal eta) b +
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
  have hsupport : orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length = eta.1.2 := by
    change SourceSupportAt t o m s v.length = eta.1.2
    rw [← htime]
    exact hcanonical.2
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath eta.1.1.external.initial.1
        eta.1.1.external.start
        (tilingInsertGapVector t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)))
        (sourceTerminal eta) := by
    rw [← sourceTerminal_eq_coordinates eta q]
    exact finitePathList_prefixedTilingInsertionPrefix
      eta.1.1.external.initial t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail rfl
  intro b hbAway
  have hbS : b.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.external.start
      eta.1.1.external.retained eta.1.2 b).1 hbAway
  have hbVTwo : b.1 ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length := by
    rw [hsupport]
    exact hbS
  have hbData := (mem_orientedTilingVTwoBases_iff t o
    (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length b.1).mp
      hbVTwo |>.1
  have hbAt := (Finset.mem_filter.mp hbData).2
  have hbase : localTime s v.length b.1 =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (sourceTerminal eta) b.1 +
        tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        (sourceTerminal eta) b b.1]
    exact tilingExternalDomino_isBase t eta.1.1.external.start
      eta.1.1.external.retained b
  have hpartner : localTime s v.length (tilingPartner t b.1) =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (sourceTerminal eta) (tilingPartner t b.1) +
        tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        (sourceTerminal eta) b (tilingPartner t b.1)]
    exact tilingPartner_ofExternalDomino_has_base t eta.1.1.external.start
      eta.1.1.external.retained b
  have hbaseLt : localTime s v.length b.1 < m :=
    (mem_shellZeroSourceTotalWindow.mp hbAt.2).2
  have hfixed : prefixedTilingFixedBoundaryLocalTime
        eta.1.1.external.initial.1 eta.1.1.external.start
        eta.1.1.external.retained (sourceTerminal eta) (tilingPartner t b.1) ≤
      prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (sourceTerminal eta) b.1 := by
    have hbDominant := hbAt.1
    rw [hbase, hpartner] at hbDominant
    omega
  unfold prefixedTilingFixedBoundaryDominoMax
  rw [max_eq_left hfixed, ← hbase]
  exact hbaseLt

/-- Accepted-clock invariance once the prefix-correct threshold set and the
local time at the common physical endpoint have been identified.  This form
also covers the unrepresented one-step terminal: its tiling base need not be
one of the distinguished insertion dominoes. -/
theorem prefixedTilingStoppingAccepted_iff_of_strictAway_of_endpointLocal
    (initial : BoundaryTail) {i cap : ℕ} (t : DominoTiling) (x : Point)
    (m k cutoff : ℕ) (hm : 0 < m) (hk : 0 < k)
    (r : TilingRetainedWord t x i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (hbelow : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (q j : ℕ)) tail) b +
        tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b < m)
    (hbelow' : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (q' j : ℕ)) tail) b +
        tilingDominoTotal t x r (fun j ↦ (q' j : ℕ)) b < m)
    (hpos : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1).length)
    (hpos' : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1).length)
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff)
    (hendpointLocal :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1
      let v' := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q' j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      let s' := trajectory (extendPrefix (directionVectorOfList v'))
      localTime s v.length (s v.length) =
        localTime s' v'.length (s' v'.length)) :
    PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
        initial.1 t x r (fun j ↦ (q j : ℕ)) tail.1 ↔
      PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
        initial.1 t x r (fun j ↦ (q' j : ℕ)) tail.1 := by
  let v := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q j : ℕ)) tail.1
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q' j : ℕ)) tail.1
  let omega := extendPrefix (directionVectorOfList v)
  let omega' := extendPrefix (directionVectorOfList v')
  let s := trajectory omega
  let s' := trajectory omega'
  have hsites : thresholdSites s v.length m =
      thresholdSites s' v'.length m := by
    exact thresholdSites_prefixedTilingInsertionPrefix_eq_of_distinguished_eq
      initial t x r tail m hm D q q' hstart hdist hbelow hbelow'
  have hcount : thresholdCount s v.length m =
      thresholdCount s' v'.length m := by
    unfold thresholdCount
    rw [hsites]
  unfold PrefixedTilingStoppingAccepted
  change truncatedLevelTime m k cutoff omega = v.length ↔
    truncatedLevelTime m k cutoff omega' = v'.length
  rw [truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff v.length omega hlt,
    truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff v'.length omega' hlt',
    thresholdCreation_iff_terminal_count_and_new_localTime
      s m k v.length hm hk hpos,
    thresholdCreation_iff_terminal_count_and_new_localTime
      s' m k v'.length hm hk hpos']
  constructor
  · rintro ⟨hc, hl⟩
    exact ⟨hcount ▸ hc, hendpointLocal ▸ hl⟩
  · rintro ⟨hc, hl⟩
    exact ⟨hcount.symm ▸ hc, hendpointLocal.symm ▸ hl⟩

/-- At every point which is above the strict-away level on at least one of
the two reconstructed paths, the complete physical local times agree
exactly. -/
theorem prefixedTilingPrefixLocalTime_eq_of_ge_level
    {i cap : ℕ} (initial : List Direction) (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (level : ℕ) (D : Finset Point)
    (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (hbelow : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial x r terminal b +
        tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b < level)
    (hbelow' : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial x r terminal b +
        tilingDominoTotal t x r (fun j ↦ (q' j : ℕ)) b < level)
    (y : Point)
    (hge : level ≤ listLocalTime
          (prefixedTilingPrefixPointPath initial x
            (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) y ∨
      level ≤ listLocalTime
          (prefixedTilingPrefixPointPath initial x
            (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal) y) :
    listLocalTime
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) y =
      listLocalTime
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal) y := by
  classical
  by_cases hrepresented :
      tilingBase t y ∈ tilingExternalDominoBases t x r
  · let b : TilingExternalDomino t x r := ⟨tilingBase t y, hrepresented⟩
    by_cases hD : b.1 ∈ D
    · exact prefixedTilingPrefixLocalTime_eq_of_distinguished_eq
        initial t x r terminal D q q' hdist y hD
    · have hends := prefixedTilingActualEndpointsBelow_of_max_add_total_lt
        initial t x r (fun j ↦ (q j : ℕ)) terminal level b (hbelow b hD)
      have hends' := prefixedTilingActualEndpointsBelow_of_max_add_total_lt
        initial t x r (fun j ↦ (q' j : ℕ)) terminal level b (hbelow' b hD)
      rcases point_eq_tilingBase_or_partner_base t y with hy | hy
      · have hyb : y = b.1 := by
          change y = tilingBase t y
          exact hy
        rw [hyb] at hge
        exact (hge.elim (fun h ↦ (Nat.not_le_of_lt hends.1 h).elim)
          (fun h ↦ (Nat.not_le_of_lt hends'.1 h).elim))
      · have hyb : y = tilingPartner t b.1 := by
          change y = tilingPartner t (tilingBase t y)
          exact hy
        rw [hyb] at hge
        exact (hge.elim (fun h ↦ (Nat.not_le_of_lt hends.2 h).elim)
          (fun h ↦ (Nat.not_le_of_lt hends'.2 h).elim))
  · rw [prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        initial t x r (fun j ↦ (q j : ℕ)) terminal y hrepresented,
      prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        initial t x r (fun j ↦ (q' j : ℕ)) terminal y hrepresented]

/-- Accepted prefixed insertion words with the same distinguished projection
and strict-away support have exactly the same favorite set.  No global
`levelFavorite` premise is used: a positive-rank creation supplies a point at
level `m`, while every local time at or above that level is fixed exactly. -/
theorem favoriteSites_prefixedInsertion_eq_of_distinguished_eq_of_strictAway
    (initial : BoundaryTail) {i cap : ℕ} (t : DominoTiling) (x : Point)
    (m k cutoff : ℕ) (hk : 0 < k)
    (r : TilingRetainedWord t x i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (hbelow : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (q j : ℕ)) tail) b +
        tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b < m)
    (hbelow' : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (q' j : ℕ)) tail) b +
        tilingDominoTotal t x r (fun j ↦ (q' j : ℕ)) b < m)
    (haccepted : PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
      initial.1 t x r (fun j ↦ (q j : ℕ)) tail.1)
    (haccepted' : PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
      initial.1 t x r (fun j ↦ (q' j : ℕ)) tail.1)
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1
    favoriteSites
        (trajectory (extendPrefix (directionVectorOfList v))) v.length =
      favoriteSites
        (trajectory (extendPrefix (directionVectorOfList v'))) v'.length := by
  let v := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q j : ℕ)) tail.1
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q' j : ℕ)) tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  let terminal := prefixedTilingInsertionTerminal initial t x r
    (fun j ↦ (q j : ℕ)) tail
  have hterminal' : prefixedTilingInsertionTerminal initial t x r
      (fun j ↦ (q' j : ℕ)) tail = terminal :=
    (prefixedTilingInsertionTerminal_eq_of_coordinates initial t x r
      (fun j ↦ (q j : ℕ)) (fun j ↦ (q' j : ℕ)) tail hstart).symm
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix initial t x r
      (fun j ↦ (q j : ℕ)) tail hstart
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal := by
    rw [← hterminal']
    exact finitePathList_prefixedTilingInsertionPrefix initial t x r
      (fun j ↦ (q' j : ℕ)) tail hstart
  have hcreation : ThresholdCreation s m k v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff v.length _ hlt).mp haccepted
  have hcreation' : ThresholdCreation s' m k v'.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff v'.length _ hlt').mp haccepted'
  have hterminalHigh : m ≤ localTime s v.length (s v.length) :=
    (mem_thresholdSites s v.length m (s v.length)).mp
      (position_mem_thresholdSites_of_creation hk hcreation) |>.2
  have hterminalHigh' : m ≤ localTime s' v'.length (s' v'.length) :=
    (mem_thresholdSites s' v'.length m (s' v'.length)).mp
      (position_mem_thresholdSites_of_creation hk hcreation') |>.2
  have hlocalEq (y : Point)
      (hge : m ≤ localTime s v.length y ∨
        m ≤ localTime s' v'.length y) :
      localTime s v.length y = localTime s' v'.length y := by
    rw [localTime_eq_listLocalTime, localTime_eq_listLocalTime,
      hpath, hpath']
    apply prefixedTilingPrefixLocalTime_eq_of_ge_level initial.1 t x r
      terminal m D q q' hdist hbelow
    · simpa only [terminal, hterminal'] using hbelow'
    · simpa only [localTime_eq_listLocalTime, hpath, hpath'] using hge
  ext y
  rw [mem_favoriteSites_iff_forall, mem_favoriteSites_iff_forall]
  constructor
  · intro hy
    have hyHigh : m ≤ localTime s v.length y :=
      hterminalHigh.trans (hy (s v.length))
    have hyEq := hlocalEq y (Or.inl hyHigh)
    intro z
    by_cases hzHigh : m ≤ localTime s' v'.length z
    · have hzEq := hlocalEq z (Or.inr hzHigh)
      rw [← hyEq, ← hzEq]
      exact hy z
    · have hzLt : localTime s' v'.length z < m := Nat.lt_of_not_ge hzHigh
      rw [← hyEq]
      exact hzLt.le.trans hyHigh
  · intro hy
    have hyHigh : m ≤ localTime s' v'.length y :=
      hterminalHigh'.trans (hy (s' v'.length))
    have hyEq := hlocalEq y (Or.inr hyHigh)
    intro z
    by_cases hzHigh : m ≤ localTime s v.length z
    · have hzEq := hlocalEq z (Or.inl hzHigh)
      rw [hyEq, hzEq]
      exact hy z
    · have hzLt : localTime s v.length z < m := Nat.lt_of_not_ge hzHigh
      rw [hyEq]
      exact hzLt.le.trans hyHigh

/-- The honest accepted-base screen reconstructs the literal first-strip
source support.  Away bases are read from its canonical broad-site equality;
distinguished bases are fixed by the selected exact witness. -/
theorem sourceSupportAt_eq_of_acceptedBase
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (candidate : Point)
    (hcandidate : candidate ∈ eta.1.2)
    (low externalLow externalHigh : ℕ) (cap : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hzero : 0 ∉ shellZeroSourceTotalWindow m (shellWidth48 m))
    (q q' : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap))
    (hdist : (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q').1)
    (hcanonical' : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted' : PrefixedTilingStoppingAccepted
      ((SourceFiber eta).stoppingTime cap) eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1)
    (ell : TruncatedTotals ((SourceFiber eta).upper cap))
    (hbase : PrefixedCanonicalDominantCandidateWindowSpec.acceptedBaseProp
      ((sourceParameters (cap := cap) eta candidate hcandidate low externalLow
        externalHigh (shellZeroSourceTotalWindow m (shellWidth48 m))).toSpec)
      ell)
    (htotal : ∀ b, tilingAwayTotal t eta.1.1.external.start
      eta.1.1.external.retained
      (supportComplementDistinguished t eta.1.1.external.start
        eta.1.1.external.retained eta.1.2)
      ((splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q).2) b = ell b) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    SourceSupportAt t o m s v.length = eta.1.2 := by
  classical
  let D := supportComplementDistinguished t eta.1.1.external.start
    eta.1.1.external.retained eta.1.2
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  let terminal := sourceTerminal eta
  have hstart : trajectory (extendPrefix (directionVectorOfList
      eta.1.1.external.initial.1)) eta.1.1.external.initial.1.length =
      eta.1.1.external.start := rfl
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath eta.1.1.external.initial.1
        eta.1.1.external.start
        (tilingInsertGapVector t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ))) terminal := by
    simpa only [terminal, sourceTerminal_eq_coordinates eta q] using
      (finitePathList_prefixedTilingInsertionPrefix
        eta.1.1.external.initial t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        eta.1.1.external.tail hstart)
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      prefixedTilingPrefixPointPath eta.1.1.external.initial.1
        eta.1.1.external.start
        (tilingInsertGapVector t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q' j : ℕ))) terminal := by
    simpa only [terminal, sourceTerminal_eq_coordinates eta q'] using
      (finitePathList_prefixedTilingInsertionPrefix
        eta.1.1.external.initial t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
        eta.1.1.external.tail hstart)
  have hupper : ∀ b,
      tilingDominoTotal t eta.1.1.external.start eta.1.1.external.retained
          (fun j ↦ (q j : ℕ)) b.1 < (SourceFiber eta).upper cap b := by
    intro b
    rw [← tilingAwayTotal_split_eq_dominoTotal t eta.1.1.external.start
      eta.1.1.external.retained D q b]
    rw [htotal b]
    exact (ell b).isLt
  have hell : reconstructedTilingAwayTotalsOfCoordinates t
      eta.1.1.external.start eta.1.1.external.retained D
      ((SourceFiber eta).upper cap) q hupper = ell := by
    funext b
    apply Fin.ext
    change tilingDominoTotal t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b.1 = ell b
    rw [← tilingAwayTotal_split_eq_dominoTotal t eta.1.1.external.start
      eta.1.1.external.retained D q b, htotal b]
  have hactual : actualCanonicalDominantBroadAwaySites t s v.length
      eta.1.1.external.start eta.1.1.external.retained D
      (shellZeroSourceTotalWindow m (shellWidth48 m)) = eta.1.2 := by
    rw [actualCanonicalDominantBroadAwaySites_eq_reconstructedPrefixed
      eta.1.1.external.initial.1 t s eta.1.1.external.start
      eta.1.1.external.retained q terminal D ((SourceFiber eta).upper cap)
      hupper hpath (shellZeroSourceTotalWindow m (shellWidth48 m)), hell]
    exact hbase.1.2.2
  have hlt' : v'.length < orientedAllCreationCoordinateCutoff eta.1.1
      ((SourceFiber eta).coordinateCap cap) :=
    prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1
      ((SourceFiber eta).coordinateCap cap) q'
  have hcreation' : ThresholdCreation s' m k v'.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m k
      (orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap)) v'.length _ hlt').mp
    exact haccepted'
  have htime' : creationTimeNat m k s' = v'.length :=
    creationTimeNat_eq_of_creation hcreation'
  have hsupport' : SourceSupportAt t o m s' v'.length = eta.1.2 := by
    rw [← htime']
    exact hcanonical'.2
  have hcode : fixedOrientedTypedExternalWordCode t o v.length s =
      eta.1.1.external := by
    exact sourceFixedExternalCode_prefixedInsertion eta hm hk
      (fun j ↦ (q j : ℕ))
  apply Finset.ext
  intro y
  constructor
  · intro hy
    have hyData := (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length y).mp hy
    have hyRaw := Finset.mem_filter.mp hyData.1
    have hyBase : IsTilingBase t y :=
      isTilingBase_of_mem_visitedTilingBases hyRaw.1
    have hrepresentedSubset := (SourceSupportData t o m k).represented
      s v.length (trajectory_mem_validStepWalk _)
    rw [hcode] at hrepresentedSubset
    have hyRepresented := hrepresentedSubset hy
    by_cases hyD : y ∈ D
    · have hlocal (z : Point) (hz : tilingBase t z = y) :
          localTime s v.length z = localTime s' v'.length z := by
        rw [localTime_eq_listLocalTime, localTime_eq_listLocalTime,
          hpath, hpath']
        apply prefixedTilingPrefixLocalTime_eq_of_distinguished_eq
          eta.1.1.external.initial.1 t eta.1.1.external.start
          eta.1.1.external.retained terminal D q q' hdist z
        simpa only [hz] using hyD
      have hbaseEq := hlocal y (by
        exact tilingExternalDomino_isBase t eta.1.1.external.start
          eta.1.1.external.retained ⟨y, hyRepresented⟩)
      have hpartnerEq := hlocal (tilingPartner t y) (by
        rw [tilingBase_partner]
        exact tilingExternalDomino_isBase t eta.1.1.external.start
          eta.1.1.external.retained ⟨y, hyRepresented⟩)
      have hyVisited' : y ∈ visitedTilingBases t s' v'.length := by
        rw [visitedTilingBases, Finset.mem_image] at hyRaw ⊢
        obtain ⟨z, hzVisited, hzBase⟩ := hyRaw.1
        refine ⟨z, ?_, hzBase⟩
        apply (mem_visitedSites_iff_localTime_pos s' v'.length z).2
        have hzEq := hlocal z hzBase
        rw [← hzEq]
        exact (mem_visitedSites_iff_localTime_pos s v.length z).1 hzVisited
      have hyRaw' : y ∈ tilingVTwoBases t
          (shellZeroSourceTotalWindow m (shellWidth48 m)) s' v'.length := by
        apply Finset.mem_filter.mpr
        refine ⟨hyVisited', ?_⟩
        exact ⟨by simpa only [hbaseEq, hpartnerEq] using hyRaw.2.1,
          by simpa only [hbaseEq] using hyRaw.2.2⟩
      have hyOriented' : y ∈ SourceSupportAt t o m s' v'.length :=
        (mem_orientedTilingVTwoBases_iff t o
          (shellZeroSourceTotalWindow m (shellWidth48 m)) s' v'.length y).2
            ⟨hyRaw', hyData.2⟩
      rw [hsupport'] at hyOriented'
      exact hyOriented'
    · rw [← hactual]
      unfold actualCanonicalDominantBroadAwaySites
      let b : TilingAwayDomino t eta.1.1.external.start
          eta.1.1.external.retained D := ⟨⟨y, hyRepresented⟩, hyD⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨b, ?_, ?_⟩, hyBase⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · simp only [Finset.mem_univ]
        unfold tilingXiPlusAt
        rw [max_eq_left hyRaw.2.1]
        exact hyRaw.2.2
      · unfold tilingDominantEndpointAt
        rw [if_pos hyRaw.2.1]
  · intro hyS
    have hyActual : y ∈ actualCanonicalDominantBroadAwaySites t s v.length
        eta.1.1.external.start eta.1.1.external.retained D
        (shellZeroSourceTotalWindow m (shellWidth48 m)) := by
      rw [hactual]
      exact hyS
    unfold actualCanonicalDominantBroadAwaySites at hyActual
    obtain ⟨hyImage, hyBase⟩ := Finset.mem_filter.mp hyActual
    obtain ⟨b, hbFiltered, hbDom⟩ := Finset.mem_image.mp hyImage
    have hbXi := (Finset.mem_filter.mp hbFiltered).2
    have hbBase : IsTilingBase t b.1.1 := by
      rw [← tilingExternalDomino_isBase t eta.1.1.external.start
        eta.1.1.external.retained b.1]
      exact isTilingBase_tilingBase t b.1.1
    have hbLe : localTime s v.length (tilingPartner t b.1.1) ≤
        localTime s v.length b.1.1 := by
      unfold tilingDominantEndpointAt at hbDom
      split at hbDom
      next hle => exact hle
      next hnot =>
        exfalso
        have hnotBase := not_isTilingBase_tilingPartner_of_isTilingBase
          t b.1.1 hbBase
        exact hnotBase (hbDom ▸ hyBase)
    have hby : b.1.1 = y := by
      unfold tilingDominantEndpointAt at hbDom
      rw [if_pos hbLe] at hbDom
      exact hbDom
    rw [← hby] at hyS ⊢
    have hbWindow : localTime s v.length b.1.1 ∈
        shellZeroSourceTotalWindow m (shellWidth48 m) := by
      unfold tilingXiPlusAt at hbXi
      rw [max_eq_left hbLe] at hbXi
      exact hbXi
    have hbVisited : b.1.1 ∈ visitedTilingBases t s v.length := by
      rw [visitedTilingBases, Finset.mem_image]
      refine ⟨b.1.1, ?_, ?_⟩
      · apply (mem_visitedSites_iff_localTime_pos s v.length b.1.1).2
        have hbne : localTime s v.length b.1.1 ≠ 0 := by
          intro hz
          apply hzero
          simpa only [hz] using hbWindow
        omega
      · exact tilingExternalDomino_isBase t eta.1.1.external.start
          eta.1.1.external.retained b.1
    have hbOriented' : b.1.1 ∈ SourceSupportAt t o m s' v'.length := by
      rw [hsupport']
      exact hyS
    have hbCompatible := (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s' v'.length b.1.1).mp
        hbOriented' |>.2
    exact (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length b.1.1).2
        ⟨Finset.mem_filter.mpr ⟨hbVisited, ⟨hbLe, hbWindow⟩⟩,
          hbCompatible⟩

/-- Concrete prefix-correct recovery certificate for one literal first-strip
source candidate.  The denominator fixes the complete broad source screen;
the numerator may later add any chosen-coordinate narrow window. -/
noncomputable def sourceRecoveryCertificate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (candidate : Point)
    (hcandidate : candidate ∈ eta.1.2)
    (low externalLow externalHigh : ℕ) (narrowWindow : Finset ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hzero : 0 ∉ shellZeroSourceTotalWindow m (shellWidth48 m)) :
    RecoveryCertificate (SourceSupportData t o m k) eta candidate where
  parameters cap := sourceParameters eta candidate hcandidate low externalLow
    externalHigh narrowWindow
  recover cap q hselected hscreen := by
    classical
    let D := supportComplementDistinguished t eta.1.1.external.start
      eta.1.1.external.retained eta.1.2
    change orientedAllCreationSelected o m k (SourceSupportAt t o m)
      eta.1.2 eta.1.1 ((SourceFiber eta).coordinateCap cap)
      ((splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained D q).1) at hselected
    rcases hselected with ⟨a', hselected⟩
    let q' : TilingCappedCoordinates eta.1.1.external.retainedCount
        ((SourceFiber eta).coordinateCap cap) :=
      (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained D).symm
          ((splitTilingCoordinatesEquiv t eta.1.1.external.start
            eta.1.1.external.retained D q).1, a')
    change orientedAllCreationStoppedAtomPredicate o m k
        (SourceSupportAt t o m) eta.1.2 eta.1.1
          ((SourceFiber eta).coordinateCap cap) q' ∧
      PrefixedTilingStoppingAccepted ((SourceFiber eta).stoppingTime cap)
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
      ((SourceFiber eta).coordinateCap cap) q' hpred' haccepted'
    rcases hscreen with ⟨ell, hell, htotal⟩
    change ∀ b : TilingAwayDomino t eta.1.1.external.start
        eta.1.1.external.retained D,
      tilingAwayTotal t eta.1.1.external.start eta.1.1.external.retained D
        ((splitTilingCoordinatesEquiv t eta.1.1.external.start
          eta.1.1.external.retained D q).2) b = ell b at htotal
    have hbase : ((sourceParameters (cap := cap) eta candidate hcandidate low
        externalLow externalHigh narrowWindow).toSpec).acceptedBaseProp ell := by
      simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedBaseAccepts,
        decide_eq_true_eq] using hell
    have hbelow : ∀ b : TilingExternalDomino t eta.1.1.external.start
        eta.1.1.external.retained, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (sourceTerminal eta) b +
        tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b < m := by
      intro b hb
      let ba : TilingAwayDomino t eta.1.1.external.start
          eta.1.1.external.retained D := ⟨b, hb⟩
      have hs := hbase.2 ba
      rw [← tilingAwayTotal_split_eq_dominoTotal t
        eta.1.1.external.start eta.1.1.external.retained D q ba,
        htotal ba]
      exact hs
    have hbelow' : ∀ b : TilingExternalDomino t eta.1.1.external.start
        eta.1.1.external.retained, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (sourceTerminal eta) b +
        tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q' j : ℕ)) b < m := by
      exact sourceCanonical_strictAway eta q' hcanonical' haccepted'
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
          (sourceTerminal eta) := by
      simpa only [sourceTerminal_eq_coordinates eta q] using
        (finitePathList_prefixedTilingInsertionPrefix
          eta.1.1.external.initial t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ))
          eta.1.1.external.tail hstart)
    have hpath' : finitePathList (pathPrefix s' v'.length) =
        prefixedTilingPrefixPointPath eta.1.1.external.initial.1
          eta.1.1.external.start
          (tilingInsertGapVector t eta.1.1.external.start
            eta.1.1.external.retained (fun j ↦ (q' j : ℕ)))
          (sourceTerminal eta) := by
      simpa only [sourceTerminal_eq_coordinates eta q'] using
        (finitePathList_prefixedTilingInsertionPrefix
          eta.1.1.external.initial t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
          eta.1.1.external.tail hstart)
    have hlt : v.length < orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap) :=
      prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap) q
    have hlt' : v'.length < orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap) :=
      prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap) q'
    have hcreation' : ThresholdCreation s' m k v'.length := by
      apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m k
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((SourceFiber eta).coordinateCap cap)) v'.length _ hlt').mp
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
        eta.1.1.external.retained (sourceTerminal eta) m D q q'
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
    have haccepted : PrefixedTilingStoppingAccepted
        ((SourceFiber eta).stoppingTime cap) eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1 := by
      have hbelowQ : ∀ b : TilingExternalDomino t eta.1.1.external.start
          eta.1.1.external.retained, b.1 ∉ D →
        prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
            eta.1.1.external.start eta.1.1.external.retained
            (prefixedTilingInsertionTerminal eta.1.1.external.initial t
              eta.1.1.external.start eta.1.1.external.retained
              (fun j ↦ (q j : ℕ)) eta.1.1.external.tail) b +
          tilingDominoTotal t eta.1.1.external.start
            eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b < m := by
        simpa only [sourceTerminal_eq_coordinates eta q] using hbelow
      have hbelowQ' : ∀ b : TilingExternalDomino t eta.1.1.external.start
          eta.1.1.external.retained, b.1 ∉ D →
        prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
            eta.1.1.external.start eta.1.1.external.retained
            (prefixedTilingInsertionTerminal eta.1.1.external.initial t
              eta.1.1.external.start eta.1.1.external.retained
              (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail) b +
          tilingDominoTotal t eta.1.1.external.start
            eta.1.1.external.retained (fun j ↦ (q' j : ℕ)) b < m := by
        simpa only [sourceTerminal_eq_coordinates eta q'] using hbelow'
      apply (prefixedTilingStoppingAccepted_iff_of_strictAway_of_endpointLocal
        eta.1.1.external.initial t eta.1.1.external.start m k
        (orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap)) (by omega) hk
        eta.1.1.external.retained eta.1.1.external.tail D q q' hstart
        hdist hbelowQ hbelowQ' hpos hpos' hlt hlt' hendpointLocal).mpr
      exact haccepted'
    have hsupport : SourceSupportAt t o m s v.length = eta.1.2 :=
      sourceSupportAt_eq_of_acceptedBase eta candidate hcandidate low
        externalLow externalHigh cap hm hk hzero q q' hdist hcanonical'
        haccepted' ell hbase htotal
    have hfavorite : favoriteSites s v.length =
        favoriteSites s' v'.length :=
      by
        have hbelowQ : ∀ b : TilingExternalDomino t
            eta.1.1.external.start eta.1.1.external.retained, b.1 ∉ D →
          prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
              eta.1.1.external.start eta.1.1.external.retained
              (prefixedTilingInsertionTerminal eta.1.1.external.initial t
                eta.1.1.external.start eta.1.1.external.retained
                (fun j ↦ (q j : ℕ)) eta.1.1.external.tail) b +
            tilingDominoTotal t eta.1.1.external.start
              eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b < m := by
          simpa only [sourceTerminal_eq_coordinates eta q] using hbelow
        have hbelowQ' : ∀ b : TilingExternalDomino t
            eta.1.1.external.start eta.1.1.external.retained, b.1 ∉ D →
          prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
              eta.1.1.external.start eta.1.1.external.retained
              (prefixedTilingInsertionTerminal eta.1.1.external.initial t
                eta.1.1.external.start eta.1.1.external.retained
                (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail) b +
            tilingDominoTotal t eta.1.1.external.start
              eta.1.1.external.retained (fun j ↦ (q' j : ℕ)) b < m := by
          simpa only [sourceTerminal_eq_coordinates eta q'] using hbelow'
        exact favoriteSites_prefixedInsertion_eq_of_distinguished_eq_of_strictAway
          eta.1.1.external.initial t eta.1.1.external.start m k
          (orientedAllCreationCoordinateCutoff eta.1.1
            ((SourceFiber eta).coordinateCap cap)) hk
          eta.1.1.external.retained eta.1.1.external.tail D q q' hstart
          hdist hbelowQ hbelowQ' haccepted haccepted' hlt hlt'
    have hcreation : ThresholdCreation s m k v.length :=
      (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m k
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((SourceFiber eta).coordinateCap cap)) v.length _ hlt).mp haccepted
    have htime' : creationTimeNat m k s' = v'.length :=
      creationTimeNat_eq_of_creation hcreation'
    have htrace' : fixedOrientedAllCreationTraceCode t o v'.length s' =
        eta.1.1 := by
      rw [← htime']
      exact hcanonical'.1.2.2
    have hexternal : fixedOrientedTypedExternalWordCode t o v.length s =
        eta.1.1.external :=
      sourceFixedExternalCode_prefixedInsertion eta hm hk
        (fun j ↦ (q j : ℕ))
    have hexternal' : fixedOrientedTypedExternalWordCode t o v'.length s' =
        eta.1.1.external := congrArg OrientedAllCreationTraceCode.external htrace'
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
              s' v'.length)) := by rw [hfavorite, hend, hexternal, hexternal']
        _ = eta.1.1.favorite := hfavorite'
    have hcanonical : s ∈ orientedAllCreationSupportTraceAtom t o m k
        (SourceSupportAt t o m) eta.1.1 eta.1.2 := by
      refine ⟨⟨trajectory_mem_validStepWalk _, ⟨v.length, hcreation.1⟩,
        ?_⟩, ?_⟩
      · rw [creationTimeNat_eq_of_creation hcreation]
        exact htrace
      · change SourceSupportAt t o m s (creationTimeNat m k s) = eta.1.2
        rw [creationTimeNat_eq_of_creation hcreation]
        exact hsupport
    refine ⟨?_, haccepted⟩
    exact atomPredicate_of_canonical_mem_accepted (SourceSupportData t o m k)
      ((SourceFiber eta).coordinateCap cap) q hcanonical haccepted

end

end Erdos1165.HLOZPrefixedCanonicalSourceAtomRecovery
