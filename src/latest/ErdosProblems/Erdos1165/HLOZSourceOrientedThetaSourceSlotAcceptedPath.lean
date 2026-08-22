/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSlotAcceptedPath
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaExternalSourceAccepted
import ErdosProblems.Erdos1165.TilingOrientedPrefixedBoundarySourceLocalTime

/-!
# Rank-stable accepted creation on one source-window slot

This file contains the pathwise transport used by the one-away source part
of Proposition 4.5.  It deliberately assumes strict below-level bounds on
the exposed away domino.  The replacement window cannot satisfy those
bounds and is therefore not covered by this theorem.
-/

namespace Erdos1165.HLOZSourceOrientedThetaSourceSlotAcceptedPath

open HLOZPathEvents HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZSourceOrientedThetaSlotAcceptedPath LazyDecomposition
open PathInsertion PreStoppingFiber PreStoppingSpatialLaw SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization TilingDistinguishedTraceInvariant
open TilingInsertedLocalTime TilingLazyDecomposition TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime TilingPrefixedStoppedProductDisintegration
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedPrefixedBoundarySourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber VariableStoppedFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Strict-away support and a fixed distinguished projection preserve the
rank-creation stopping condition.  The endpoint local time is recovered from
the same strict-away threshold profile, so no full favorite trace is fixed. -/
theorem prefixedTilingStoppingAccepted_of_strictAway
    (initial : BoundaryTail) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (m k cutoff : ℕ)
    (hm : 1 < m) (hk : 0 < k)
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
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff)
    (haccepted' : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k cutoff) initial.1 t x r
        (fun j ↦ (q' j : ℕ)) tail.1) :
    PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k cutoff) initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1 := by
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
  have hcreation' : ThresholdCreation s' m k v'.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff v'.length _ hlt').mp haccepted'
  have hterminalHigh' : m ≤ localTime s' v'.length (s' v'.length) :=
    (mem_thresholdSites s' v'.length m (s' v'.length)).mp
      (position_mem_thresholdSites_of_creation hk hcreation') |>.2
  have hendpoint : s v.length = s' v'.length :=
    prefixedTilingInsertionEndpoint_eq_of_coordinates initial t x r
      (fun j ↦ (q j : ℕ)) (fun j ↦ (q' j : ℕ)) tail hstart
  have hendpointLocal : localTime s v.length (s v.length) =
      localTime s' v'.length (s' v'.length) := by
    rw [localTime_eq_listLocalTime, localTime_eq_listLocalTime, hpath, hpath']
    rw [hendpoint]
    apply prefixedTilingPrefixLocalTime_eq_of_ge_level initial.1 t x r
      terminal m D q q' hdist hbelow
    · simpa only [terminal, hterminal'] using hbelow'
    · exact Or.inr (by
        simpa only [localTime_eq_listLocalTime, hpath'] using hterminalHigh')
  have hpos' : 0 < v'.length := by
    by_contra hn
    have hzero : v'.length = 0 := Nat.eq_zero_of_not_pos hn
    have hlocalZero : localTime s' 0 (s' 0) = 1 := by
      simp [localTime, localTimePrefix, pathPrefix]
    rw [hzero, hlocalZero] at hterminalHigh'
    omega
  have hterminalHigh : m ≤ localTime s v.length (s v.length) := by
    rw [hendpointLocal]
    exact hterminalHigh'
  have hpos : 0 < v.length := by
    by_contra hn
    have hzero : v.length = 0 := Nat.eq_zero_of_not_pos hn
    have hlocalZero : localTime s 0 (s 0) = 1 := by
      simp [localTime, localTimePrefix, pathPrefix]
    rw [hzero, hlocalZero] at hterminalHigh
    omega
  exact (prefixedTilingStoppingAccepted_iff_of_strictAway_of_endpointLocal
    initial t x m k cutoff (by omega) hk r tail D q q' hstart hdist hbelow hbelow'
      hpos hpos' hlt hlt' hendpointLocal).mpr haccepted'

/-- The prefix-correct boundary local time equals retained multiplicity on
any nonempty external atom, not only on the all-represented support view. -/
theorem prefixedBoundaryLocalTime_eq_coordinateCard_external
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (eta : TilingOrientedExternalAllCreationStoppedCoordinate.SupportedIndex
      t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k)
    (q : Fin (eta.1.1.retainedCount + 1) → ℕ)
    (b : TilingExternalDomino t eta.1.1.start eta.1.1.retained)
    (hb : OrientationCompatible o b.1) :
    prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained
        (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
          eta.1.1.retained q eta.1.1.tail) b.1 =
      Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b) := by
  have heta_nonempty :
      (allRepresentedExternalCreationTraceAtom t o m k eta.1.1).Nonempty := by
    rcases eta.2 with ⟨s, hs⟩
    rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
    exact ⟨s, hs.1, hs.2.1, hs.2.2.1⟩
  exact prefixedBoundaryLocalTime_eq_coordinateCard
    (⟨eta.1.1, heta_nonempty⟩ :
      TilingOrientedAllRepresentedExternalFiber.SupportedIndex t o m k)
    hm hk q b hb

/-- Physical `V₂` dominance on a reconstructed external word is exactly
dominance of its fixed prefixed boundary; insertion totals cancel from the
two endpoints. -/
theorem prefixedBoundary_partner_le_base_of_vTwo_external
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (eta : TilingOrientedExternalAllCreationStoppedCoordinate.SupportedIndex
      t o m k supportAt)
    (q : TilingCappedCoordinates eta.1.1.retainedCount cap)
    (window : Finset ℕ)
    (b : TilingExternalDomino t eta.1.1.start eta.1.1.retained)
    (hVTwo :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
          eta.1.1.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingVTwoAt t window s v.length b.1) :
    prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained
        (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
          eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail)
        (tilingPartner t b.1) ≤
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained
        (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
          eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail) b.1 := by
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let terminal := prefixedTilingInsertionTerminal eta.1.1.initial t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath eta.1.1.initial.1 eta.1.1.start
        (tilingInsertGapVector t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ))) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail rfl
  have hbase : localTime s v.length b.1 =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained terminal b.1 +
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) b := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) terminal b b.1]
    exact tilingExternalDomino_isBase t eta.1.1.start eta.1.1.retained b
  have hpartner : localTime s v.length (tilingPartner t b.1) =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained terminal (tilingPartner t b.1) +
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) b := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) terminal b (tilingPartner t b.1)]
    exact tilingPartner_ofExternalDomino_has_base t eta.1.1.start
      eta.1.1.retained b
  have hdominance := hVTwo.1
  rw [hbase, hpartner] at hdominance
  change prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
      eta.1.1.retained terminal (tilingPartner t b.1) ≤
    prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
      eta.1.1.retained terminal b.1
  omega

/-- The fixed-boundary dominance recovered from one physical `V₂` witness
is independent of the inserted coordinate vector.  The optional terminal is
the same for every insertion vector in a fixed prefixed retained word. -/
theorem prefixedBoundary_partner_le_base_of_vTwo_external_all_coordinates
    {t : DominoTiling} {o : Orientation} {m k cap cap' : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (eta : TilingOrientedExternalAllCreationStoppedCoordinate.SupportedIndex
      t o m k supportAt)
    (q₀ : TilingCappedCoordinates eta.1.1.retainedCount cap)
    (window : Finset ℕ)
    (b : TilingExternalDomino t eta.1.1.start eta.1.1.retained)
    (hVTwo :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q₀ j : ℕ))
          eta.1.1.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingVTwoAt t window s v.length b.1)
    (q : TilingCappedCoordinates eta.1.1.retainedCount cap') :
    prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained
        (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
          eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail)
        (tilingPartner t b.1) ≤
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained
        (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
          eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail) b.1 := by
  have hdominance :=
    prefixedBoundary_partner_le_base_of_vTwo_external eta q₀ window b hVTwo
  have hterminal :
      prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
          eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail =
        prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
          eta.1.1.retained (fun j ↦ (q₀ j : ℕ)) eta.1.1.tail :=
    prefixedTilingInsertionTerminal_eq_of_coordinates eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
      (fun j ↦ (q₀ j : ℕ)) eta.1.1.tail rfl
  simpa only [hterminal] using hdominance

end

end Erdos1165.HLOZSourceOrientedThetaSourceSlotAcceptedPath
