/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceSelectedCarrier

set_option linter.style.haveILetI false

/-!
# Accepted creation on a singleton source-Theta slot

The source part of restricted Theta lies strictly below level `m`.  On a
singleton oriented support, physical `V₂` dominance identifies the fixed
boundary with the retained-coordinate multiplicity.  Consequently every
source-window total is strictly below level on the sole away domino.  The
rank-creation stopping condition can therefore be transported between the
literal selected witness and every coordinate vector in the same total
class.

This argument applies only to the rank-stable source window.  The replacement
window above `m` is intentionally absent.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSourceOrientedThetaSourceSingletonAccepted

open FiniteDominoProductLaw
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalSourceAccepted
open HLOZSourceOrientedThetaSourceSelectedCarrier
open HLOZSourceOrientedThetaSourceSlotAcceptedPath
open HLOZSourceOrientedThetaSourceWindowProduct
open HLOZSourceOrientedThetaSlotAcceptedPath HLOZShellZeroReplacementWindows
open HLOZPathEvents HLOZProposition48Candidates
open LazyDecomposition PathInsertion SpatialInsertionFiber
open PreStoppingFiber PreStoppingSpatialLaw StoppedInsertion
open TilingCappedMarginalization TilingLazyDecomposition
open TilingInsertedLocalTime
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem away_eq_of_singleton_support
    {t : DominoTiling} {i : ℕ} {x : Point}
    {r : TilingRetainedWord t x i} {S : Finset Point} {b : Point}
    (hS : S = {b})
    (c d : TilingAwayDomino t x r
      (supportComplementDistinguished t x r S)) : c = d := by
  apply Subtype.ext
  apply Subtype.ext
  have hc := (away_mem_support_iff t x r S c.1).1 c.2
  have hd := (away_mem_support_iff t x r S d.1).1 d.2
  have hc' : c.1.1 ∈ ({b} : Finset Point) := by
    simpa only [hS] using hc
  have hd' : d.1.1 ∈ ({b} : Finset Point) := by
    simpa only [hS] using hd
  exact (Finset.mem_singleton.mp hc').trans (Finset.mem_singleton.mp hd').symm

private theorem source_bad_at_every_away_of_singleton
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t} {b : Point}
    (data : Spec t o m k supportAt S z)
    (hS : S = {b}) (w externalLow externalHigh cap : ℕ)
    (ell : TruncatedTotals (data.upper cap))
    (hbad : externalSourceThetaAccepts data w externalLow externalHigh cap ell =
      true)
    (c : TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) :
    sourceThetaCoordinateBad m w externalLow externalHigh
      (Fintype.card (TilingCoordinatesAt t z.start z.retained c.1))
      (ell c) := by
  rw [externalSourceThetaAccepts, decide_eq_true_eq] at hbad
  rcases hbad with ⟨d, hd⟩
  have hdc : d = c := away_eq_of_singleton_support hS d c
  subst d
  exact hd

/-- Honest accepted-creation base screen for one rank-stable source slot.
The `V₂` witness is used only for fixed-boundary dominance; terminal
independence then makes it valid for every coordinate vector in the fibre. -/
theorem externalAcceptedCreationAtTotals_of_singleton_source
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point)
    (support_code : ∀ s n, supportAt s n = supportOfCode
      (fixedOrientedTypedExternalWordCode t o n s))
    (eta : SupportedIndex t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k) (cap w externalLow externalHigh : ℕ)
    (b : Point) (hS : eta.1.2 = {b})
    (hb : b ∈ tilingExternalDominoBases t eta.1.1.start eta.1.1.retained)
    (hcompat : OrientationCompatible o b)
    (q₀ : TilingCappedCoordinates eta.1.1.retainedCount
      ((concreteFiber o m k supportAt supportData eta).coordinateCap cap))
    (window : Finset ℕ)
    (hVTwo :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q₀ j : ℕ))
          eta.1.1.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingVTwoAt t window s v.length b)
    (ell : TruncatedTotals
      ((withExternalSourceSelected
        (concreteFiber o m k supportAt supportData eta)
          w externalLow externalHigh).upper cap))
    (hbad : externalSourceThetaAccepts
      (withExternalSourceSelected
        (concreteFiber o m k supportAt supportData eta)
          w externalLow externalHigh)
      w externalLow externalHigh cap ell = true) :
    externalAcceptedCreationAtTotals
      (withExternalSourceSelected
        (concreteFiber o m k supportAt supportData eta)
          w externalLow externalHigh) cap ell := by
  classical
  let data := concreteFiber o m k supportAt supportData eta
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  let bext : TilingExternalDomino t eta.1.1.start eta.1.1.retained := ⟨b, hb⟩
  intro q hselected htotal
  change externalSourceSelected data w externalLow externalHigh cap
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2) q).1) at hselected
  rcases hselected with ⟨a', ell', hatom', haccepted', hbad', htotal'⟩
  let q' := (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)).symm
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2) q).1, a')
  have hdist :
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) q).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) q').1 := by
    simp only [q', Equiv.apply_symm_apply]
  have hdom : ∀ qx : TilingCappedCoordinates eta.1.1.retainedCount
      (data.coordinateCap cap),
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained
          (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
            eta.1.1.retained (fun j ↦ (qx j : ℕ)) eta.1.1.tail)
          (tilingPartner t b) ≤
        prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained
          (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
            eta.1.1.retained (fun j ↦ (qx j : ℕ)) eta.1.1.tail) b := by
    intro qx
    exact prefixedBoundary_partner_le_base_of_vTwo_external_all_coordinates
      eta q₀ window bext hVTwo qx
  have strictAway : ∀
      (qx : TilingCappedCoordinates eta.1.1.retainedCount
        (data.coordinateCap cap))
      (ellx : TruncatedTotals (data.upper cap)),
      externalSourceThetaAccepts data w externalLow externalHigh cap ellx = true →
      (∀ c, tilingAwayTotal t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2)
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) qx).2) c = ellx c) →
      ∀ c : TilingExternalDomino t eta.1.1.start eta.1.1.retained,
        c.1 ∉ supportComplementDistinguished t eta.1.1.start
            eta.1.1.retained eta.1.2 →
        prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1 eta.1.1.start
            eta.1.1.retained
            (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
              eta.1.1.retained (fun j ↦ (qx j : ℕ)) eta.1.1.tail) c +
          tilingDominoTotal t eta.1.1.start eta.1.1.retained
            (fun j ↦ (qx j : ℕ)) c < m := by
    intro qx ellx hbadx htotalx c hcaway
    let ca : TilingAwayDomino t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) := ⟨c, hcaway⟩
    have hcS := (away_mem_support_iff t eta.1.1.start eta.1.1.retained
      eta.1.2 c).1 hcaway
    have hcb : c.1 = b := by
      rw [hS, Finset.mem_singleton] at hcS
      exact hcS
    have hccompat : OrientationCompatible o c.1 := by simpa only [hcb] using hcompat
    have hboundary := prefixedBoundaryLocalTime_eq_coordinateCard_external
      eta hm hk (fun j ↦ (qx j : ℕ)) c hccompat
    have hdominance :
        prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
            eta.1.1.retained
            (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
              eta.1.1.retained (fun j ↦ (qx j : ℕ)) eta.1.1.tail)
            (tilingPartner t c.1) ≤
          prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
            eta.1.1.retained
            (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
              eta.1.1.retained (fun j ↦ (qx j : ℕ)) eta.1.1.tail) c.1 := by
      simpa only [hcb] using hdom qx
    have hsource := source_bad_at_every_away_of_singleton data hS w
      externalLow externalHigh cap ellx hbadx ca
    rw [sourceThetaCoordinateBad, mem_shellZeroSourceFailureWindow] at hsource
    have hsourceUpper : ellx ca < m -
        Fintype.card (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained c) := by
      simpa only [ca] using hsource.1.2
    have htotalDomino :
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
            (fun j ↦ (qx j : ℕ)) c = ellx ca := by
      rw [← htotalx ca]
      exact (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
        eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) qx ca).symm
    unfold prefixedTilingFixedBoundaryDominoMax
    rw [max_eq_left hdominance, hboundary, htotalDomino]
    omega
  have hbelow := strictAway q ell hbad htotal
  have hawayq' :
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) q').2 = a' := by
    exact congrArg Prod.snd
      (Equiv.apply_symm_apply
        (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2))
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) q).1, a'))
  have htotalq' : ∀ c, tilingAwayTotal t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) q').2) c = ell' c := by
    rw [hawayq']
    exact htotal'
  have hbelow' := strictAway q' ell' hbad' htotalq'
  let dummy : TilingCreationFavoriteData := ((∅, ∅),
    (eta.1.1.start, eta.1.1.start))
  have hlt : (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
      eta.1.1.tail.1).length <
        externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) q
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hlt' : (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q' j : ℕ))
      eta.1.1.tail.1).length <
        externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) q'
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have haccepted : PrefixedTilingStoppingAccepted (data.stoppingTime cap)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 := by
    change PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
    exact prefixedTilingStoppingAccepted_of_strictAway eta.1.1.initial t
      eta.1.1.start m k
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)) hm hk
      eta.1.1.retained eta.1.1.tail
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained eta.1.2)
      q q' rfl hdist hbelow hbelow' hlt hlt' haccepted'
  refine ⟨?_, haccepted⟩
  exact concreteFiber_atomPredicate_of_accepted supportData supportOfCode
    support_code eta hm hk cap q haccepted

/-- A literal reconstructed coordinate whose selected base is in physical
`V₂`, whose complete base local time is in the below-level source strip,
and whose retained external count fails the balance window belongs to the
strengthened accepted source-Theta predicate. -/
theorem externalAcceptedSourceThetaPredicate_of_singleton_source
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point)
    (support_code : ∀ s n, supportAt s n = supportOfCode
      (fixedOrientedTypedExternalWordCode t o n s))
    (eta : SupportedIndex t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k) (cap w externalLow externalHigh : ℕ)
    (b : Point) (hS : eta.1.2 = {b})
    (hb : b ∈ tilingExternalDominoBases t eta.1.1.start eta.1.1.retained)
    (hcompat : OrientationCompatible o b)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((concreteFiber o m k supportAt supportData eta).coordinateCap cap))
    (haccepted : PrefixedTilingStoppingAccepted
      ((concreteFiber o m k supportAt supportData eta).stoppingTime cap)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.tail.1)
    (window : Finset ℕ)
    (hVTwo :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
          eta.1.1.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingVTwoAt t window s v.length b)
    (hsource :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
          eta.1.1.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      localTime s v.length b ∈ shellZeroSourceTotalWindow m w)
    (hexternal : ¬(externalLow ≤
        Fintype.card (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained
          ⟨b, hb⟩) ∧
      Fintype.card (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained
          ⟨b, hb⟩) < externalHigh)) :
    let data := concreteFiber o m k supportAt supportData eta
    let sourceData := withExternalSourceSelected data w externalLow externalHigh
    externalAcceptedSourceThetaPredicate sourceData w externalLow externalHigh
      cap q := by
  classical
  dsimp only
  let data := concreteFiber o m k supportAt supportData eta
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  let D := supportComplementDistinguished t eta.1.1.start eta.1.1.retained
    eta.1.2
  let bext : TilingExternalDomino t eta.1.1.start eta.1.1.retained := ⟨b, hb⟩
  have hbS : b ∈ eta.1.2 := by rw [hS]; simp
  have hbaway : bext.1 ∉ D :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 bext).2 hbS
  let ba : TilingAwayDomino t eta.1.1.start eta.1.1.retained D :=
    ⟨bext, hbaway⟩
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
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
      eta.1.1.tail rfl
  have hlocal : localTime s v.length b =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained terminal b +
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) bext := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) terminal bext b]
    exact tilingExternalDomino_isBase t eta.1.1.start eta.1.1.retained bext
  have hboundary :
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained terminal b =
        Fintype.card (TilingCoordinatesAt t eta.1.1.start
          eta.1.1.retained bext) := by
    simpa only [terminal, bext] using
      (prefixedBoundaryLocalTime_eq_coordinateCard_external eta hm hk
        (fun j ↦ (q j : ℕ)) bext hcompat)
  have hsource' : localTime s v.length b ∈
      shellZeroSourceTotalWindow m w := by simpa only [s, v] using hsource
  rw [mem_shellZeroSourceTotalWindow] at hsource'
  have htotal_lt_m :
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) bext < m := by omega
  have htotal_upper : ∀ c : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained D,
      tilingAwayTotal t eta.1.1.start eta.1.1.retained D
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).2) c <
          sourceData.upper cap c := by
    intro c
    have hcb : c = ba := away_eq_of_singleton_support hS c ba
    subst c
    change tilingAwayTotal t eta.1.1.start eta.1.1.retained D
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).2) ba <
        max eta.1.1.retainedCount (m + shellWidth48 m) + 1
    calc
      tilingAwayTotal t eta.1.1.start eta.1.1.retained D
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).2) ba =
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) bext :=
        tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
          eta.1.1.retained D q ba
      _ < m := htotal_lt_m
      _ < max eta.1.1.retainedCount (m + shellWidth48 m) + 1 := by omega
  let ell : TruncatedTotals (sourceData.upper cap) := fun c ↦
    ⟨tilingAwayTotal t eta.1.1.start eta.1.1.retained D
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).2) c,
      htotal_upper c⟩
  have hellTotal : ∀ c, tilingAwayTotal t eta.1.1.start
      eta.1.1.retained D
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).2) c =
        ell c := fun _ ↦ rfl
  have hbaTotal : ell ba = tilingDominoTotal t eta.1.1.start
      eta.1.1.retained (fun j ↦ (q j : ℕ)) bext := by
    change tilingAwayTotal t eta.1.1.start eta.1.1.retained D
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).2) ba = _
    exact tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
      eta.1.1.retained D q ba
  have hsourceBad : sourceThetaCoordinateBad m w externalLow externalHigh
      (Fintype.card (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained
        bext)) (ell ba) := by
    rw [sourceThetaCoordinateBad, mem_shellZeroSourceFailureWindow, hbaTotal]
    refine ⟨⟨?_, ?_⟩, hexternal⟩ <;> omega
  have hbad : externalSourceThetaAccepts sourceData w externalLow externalHigh
      cap ell = true := by
    rw [externalSourceThetaAccepts, decide_eq_true_eq]
    exact ⟨ba, hsourceBad⟩
  refine ⟨?_, ⟨ell, ?_, hellTotal⟩⟩
  · exact concreteFiber_atomPredicate_of_accepted supportData supportOfCode
      support_code eta hm hk cap q haccepted
  · exact ⟨externalAcceptedCreationAtTotals_of_singleton_source
      supportData supportOfCode support_code eta hm hk cap w externalLow
      externalHigh b hS hb hcompat q window hVTwo ell hbad, hbad⟩

/-- Exact carrier-weighted mass identity for the strengthened source
selector.  This theorem does not use a broad atom-to-selector implication:
the source-bad screened coordinate itself constructs the selected witness. -/
theorem externalSourceSelectedStoppedGeometricMass_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ) :
    let sourceData := withExternalSourceSelected data w externalLow externalHigh
    prefixedTilingStoppedAcceptedGeometricMass
        (sourceData.stoppingTime cap) z.initial.1 t z.start z.retained
        (sourceData.coordinateCap cap) z.tail.1
        (externalAcceptedSourceThetaPredicate sourceData w externalLow
          externalHigh cap) =
      externalAcceptedSourceThetaScreenMass sourceData w externalLow
          externalHigh cap *
        externalAcceptedThetaCarrier sourceData cap := by
  classical
  dsimp only
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  letI : Fintype (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) :=
    instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
  letI : Fintype (TilingDistinguishedDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) :=
    instFintypeTilingDistinguishedDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
  have h := @prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
    (sourceData.stoppingTime cap) z.initial.1 z.retainedCount
    (sourceData.coordinateCap cap) t z.start z.retained z.tail.1
    (externalAcceptedSourceThetaPredicate sourceData w externalLow
      externalHigh cap)
    (Classical.decPred _)
    (supportComplementDistinguished t z.start z.retained S)
    (sourceData.selected cap) (Classical.decPred _) (sourceData.upper cap)
    (externalAcceptedSourceThetaAtTotals sourceData w externalLow
      externalHigh cap)
    (Classical.decPred _)
    (externalSourceSelectedPredicate_factorization data w externalLow
      externalHigh cap)
    (by
      apply ne_of_gt
      apply Finset.sum_pos'
      · intro ell _hell
        exact Finset.prod_nonneg fun b _ ↦
          tilingAwayExactTotalMass_nonneg t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) b (ell b)
      · let zero : TruncatedTotals (sourceData.upper cap) :=
          fun b ↦ ⟨0, sourceData.upper_pos cap b⟩
        refine ⟨zero, Finset.mem_univ _, ?_⟩
        unfold jointMass
        apply Finset.prod_pos
        intro b _hb
        exact tilingAwayExactTotalMass_zero_pos t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S) b)
  simpa only [externalAcceptedSourceThetaScreenMass,
    externalAcceptedThetaCarrier, tilingDistinguishedAssignmentMass] using h

/-- Checked one-coordinate source cost, multiplied by the exact strengthened
distinguished carrier. -/
theorem externalSourceSelectedStoppedGeometricMass_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (arith : HLOZSourceOrientedThetaExternalProduct.ExternalThetaProductArithmetic
      (withExternalSourceSelected data w externalLow externalHigh)
        w externalLow externalHigh cap) :
    let sourceData := withExternalSourceSelected data w externalLow externalHigh
    prefixedTilingStoppedAcceptedGeometricMass
        (sourceData.stoppingTime cap) z.initial.1 t z.start z.retained
        (sourceData.coordinateCap cap) z.tail.1
        (externalAcceptedSourceThetaPredicate sourceData w externalLow
          externalHigh cap) ≤
      (2 * ∑ b, HLOZSourceOrientedThetaExternalProduct.externalThetaCost
        sourceData cap b) * externalAcceptedThetaCarrier sourceData cap := by
  dsimp only
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  change prefixedTilingStoppedAcceptedGeometricMass
      (sourceData.stoppingTime cap) z.initial.1 t z.start z.retained
      (sourceData.coordinateCap cap) z.tail.1
      (externalAcceptedSourceThetaPredicate sourceData w externalLow
        externalHigh cap) ≤
    (2 * ∑ b, HLOZSourceOrientedThetaExternalProduct.externalThetaCost
      sourceData cap b) * externalAcceptedThetaCarrier sourceData cap
  rw [externalSourceSelectedStoppedGeometricMass_eq data w externalLow
    externalHigh cap]
  exact mul_le_mul_of_nonneg_right
    ((externalAcceptedSourceThetaScreenMass_le_externalThetaScreenMass
      sourceData w externalLow externalHigh cap).trans
      (HLOZSourceOrientedThetaExternalProduct.externalThetaScreenMass_le
        sourceData w externalLow externalHigh cap arith))
    (externalAcceptedThetaCarrier_nonneg sourceData cap)

end

end Erdos1165.HLOZSourceOrientedThetaSourceSingletonAccepted
