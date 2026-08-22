/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedDeltaScreenGeometricBound
import ErdosProblems.Erdos1165.TilingOrientedAllCreationConcreteFamily
import ErdosProblems.Erdos1165.TilingShellZeroStaticSupportCoordinateIff
import ErdosProblems.Erdos1165.TilingShellZeroSupportedSourceStaticFacts

/-!
# One-sided literal source screen on a supported static carrier

Exact source-atom membership implies the pure all-`I₁` coordinate screen.
No converse is asserted.  This is precisely the source hypothesis consumed
by the delta-indexed geometric lemma.
-/

namespace Erdos1165.TilingShellZeroSourceScreenForward

open FiniteDominoProductLaw HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroExternalWindow
open HLOZShellZeroReplacementWindows LazyDecomposition
open PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingInsertedLocalTime
open TilingLazyDecomposition TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroExternalStaticSupportData
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroFactoredCapScreen
open TilingShellZeroSourcePartition
open TilingShellZeroStaticSupportCoordinateIff
open TilingShellZeroSupportedSourceStaticFacts
open TilingSpatialInsertionFiber TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def coordinateCap {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t) (m cap : ℕ) : ℕ :=
  max z.retainedCount (m + shellWidth48 m) + cap

def coordinateUpper {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t) (m : ℕ)
    (_b : TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained ∅)) : ℕ :=
  max z.retainedCount (m + shellWidth48 m) + 1

/-- The actual common distinguished carrier is the represented complement
of the static moved support. -/
def staticD {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    Finset Point := supportComplementDistinguished t z.start z.retained S

def upper {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) (m : ℕ)
    (_b : TilingAwayDomino t z.start z.retained (staticD z S)) : ℕ :=
  max z.retainedCount (m + shellWidth48 m) + 1

def sourceStoppingTime {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t) (m k cap : ℕ) :
    StepPath → ℕ :=
  truncatedLevelTime m k (externalCoordinateCutoff z (coordinateCap z m cap))

def canonicalPath {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t)
    (q : Fin (z.retainedCount + 1) → ℕ) : WalkPath :=
  trajectory (extendPrefix (directionVectorOfList
    (prefixedTilingInsertionPrefixList z.initial.1 t z.start z.retained q
      z.tail.1)))

def sourcePredicate
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total cap : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point)
    (q : TilingCappedCoordinates z.retainedCount (coordinateCap z m cap)) : Prop :=
  canonicalPath z (fun j ↦ (q j : ℕ)) ∈
    orientedValidShellZeroExactSourceStaticSupportAtom t o m k
      (shellWidth48 m) low externalLow externalHigh total z S

def selected
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total cap : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point)
    (d : TilingDistinguishedCoordinates (cap := coordinateCap z m cap)
      t z.start z.retained (staticD z S)) : Prop :=
  ∃ a, let q := (splitTilingCoordinatesEquiv t z.start z.retained
      (staticD z S)).symm (d, a)
    sourcePredicate t o m k low externalLow externalHigh total cap z S q ∧
      PrefixedTilingStoppingAccepted (sourceStoppingTime z m k cap)
        z.initial.1 t z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1

def sourceScreen
    (t : DominoTiling) (m cap : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point)
    (ell : TruncatedTotals (upper z S m)) : Prop :=
  allSourceVector (fun b v ↦ tilingShellZeroSourceCoordinate
    (cap := coordinateCap z m cap) (m := m) (w := shellWidth48 m)
      t z.start z.retained (staticD z S) (upper z S m) b v) ell

/-- Every capped prefixed reconstruction lies strictly below the common
external-word cutoff. -/
theorem insertion_lt_cutoff
    {t : DominoTiling} (z : OrientedTilingTypedExternalWordCode t)
    (m cap : ℕ)
    (q : TilingCappedCoordinates z.retainedCount (coordinateCap z m cap)) :
    (prefixedTilingInsertionPrefixList z.initial.1 t z.start z.retained
      (fun j ↦ (q j : ℕ)) z.tail.1).length <
        externalCoordinateCutoff z (coordinateCap z m cap) := by
  let favorite : TilingCreationFavoriteData := ((∅, ∅), (z.start, z.start))
  have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
    (withFavorite z favorite) (coordinateCap z m cap) q
  change (prefixedTilingInsertionPrefixList z.initial.1 t z.start z.retained
      (fun j ↦ (q j : ℕ)) z.tail.1).length <
        externalCoordinateCutoff z (coordinateCap z m cap) at hraw
  exact hraw

/-- Acceptance at the source clock identifies its creation time with the
physical prefixed insertion length. -/
theorem source_creation_time_eq
    {t : DominoTiling} {m k cap : ℕ}
    (z : OrientedTilingTypedExternalWordCode t)
    (q : TilingCappedCoordinates z.retainedCount (coordinateCap z m cap))
    (haccepted : PrefixedTilingStoppingAccepted (sourceStoppingTime z m k cap)
      z.initial.1 t z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1) :
    creationTimeNat m k (canonicalPath z (fun j ↦ (q j : ℕ))) =
      (prefixedTilingInsertionPrefixList z.initial.1 t z.start z.retained
        (fun j ↦ (q j : ℕ)) z.tail.1).length := by
  let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start z.retained
    (fun j ↦ (q j : ℕ)) z.tail.1
  have hcreation : ThresholdCreation
      (canonicalPath z (fun j ↦ (q j : ℕ))) m k v.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (externalCoordinateCutoff z (coordinateCap z m cap)) v.length
      (extendPrefix (directionVectorOfList v)) (insertion_lt_cutoff z m cap q)).mp
    exact haccepted
  exact creationTimeNat_eq_of_creation hcreation

/-- Source exact-atom membership transports endpoint dominance to the
prefix-correct fixed boundary counts on every static-support coordinate. -/
theorem boundary_dominance_of_source
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total cap : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (hm : 1 < m) (hk : 0 < k)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      (coordinateCap eta.1.1 m cap))
    (hsource : sourcePredicate t o m k low externalLow externalHigh total cap
      eta.1.1 eta.1.2 q)
    (haccepted : PrefixedTilingStoppingAccepted
      (sourceStoppingTime eta.1.1 m k cap) eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
          eta.1.1.tail.1) :
    ∀ b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2),
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained
          (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
            eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail)
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained
          (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
            eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail) b.1.1 := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
  let s := canonicalPath eta.1.1 (fun j ↦ (q j : ℕ))
  have htime := source_creation_time_eq eta.1.1 q haccepted
  have hsupport := hsource.2
  change sourceStaticSupport t o m k (shellWidth48 m) s = eta.1.2 at hsupport
  rw [sourceStaticSupport, htime] at hsupport
  intro b
  have hbS : b.1.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b.1).1 b.2
  have hbOriented : b.1.1 ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length := by
    rw [hsupport]
    exact hbS
  have hbRaw := (mem_orientedTilingVTwoBases_iff t o
    (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length b.1.1).mp
      hbOriented |>.1
  change b.1.1 ∈ (visitedTilingBases t s v.length).filter
    (tilingVTwoAt t (shellZeroSourceTotalWindow m (shellWidth48 m))
      s v.length) at hbRaw
  have hV := (Finset.mem_filter.mp hbRaw).2
  let terminal := prefixedTilingInsertionTerminal eta.1.1.initial t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath eta.1.1.initial.1 eta.1.1.start
        (tilingInsertGapVector t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ))) terminal :=
    finitePathList_prefixedTilingInsertionPrefix eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail rfl
  have hbaseLocal : localTime s v.length b.1.1 =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained terminal b.1.1 +
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) b.1 := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) terminal b.1 b.1.1
        (tilingExternalDomino_isBase t eta.1.1.start eta.1.1.retained b.1)]
  have hpartnerLocal : localTime s v.length (tilingPartner t b.1.1) =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained terminal (tilingPartner t b.1.1) +
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) b.1 := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) terminal b.1 (tilingPartner t b.1.1)
        (tilingPartner_ofExternalDomino_has_base t eta.1.1.start
          eta.1.1.retained b.1)]
  have hdom := hV.1
  rw [hbaseLocal, hpartnerLocal] at hdom
  have hboundary :
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained terminal (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained terminal b.1.1 :=
    Nat.le_of_add_le_add_right hdom
  simpa only [terminal] using hboundary

/-- Literal exact-source membership is contained in the pure source product
screen, with the same distinguished selector used by every delta piece. -/
theorem source_forward
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total cap : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (hm : 1 < m) (hk : 0 < k)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      (coordinateCap eta.1.1 m cap))
    (hq : sourcePredicate t o m k low externalLow externalHigh total cap
          eta.1.1 eta.1.2 q ∧
      PrefixedTilingStoppingAccepted (sourceStoppingTime eta.1.1 m k cap)
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) eta.1.1.tail.1) :
    selected t o m k low externalLow externalHigh total cap eta.1.1 eta.1.2
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (staticD eta.1.1 eta.1.2) q).1) ∧
      TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2) (upper eta.1.1 eta.1.2 m)
        (sourceScreen t m cap eta.1.1 eta.1.2)
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (staticD eta.1.1 eta.1.2) q).2) := by
  classical
  refine ⟨?_, ?_⟩
  · refine ⟨(splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (staticD eta.1.1 eta.1.2) q).2, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hq
  · let support := coordinateSupportData t o m k (shellWidth48 m) low
      externalLow externalHigh total cap eta hm
    have hwindow := support.toWindowData hexternal
    have htime := source_creation_time_eq eta.1.1 q hq.2
    let s := canonicalPath eta.1.1 (fun j ↦ (q j : ℕ))
    let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
    have hsupport := hq.1.2
    change sourceStaticSupport t o m k (shellWidth48 m) s = eta.1.2 at hsupport
    rw [sourceStaticSupport, htime] at hsupport
    have hfailure : ∀ b : TilingAwayDomino t eta.1.1.start
        eta.1.1.retained (staticD eta.1.1 eta.1.2),
      tilingVTwoAt t (shellZeroSourceTotalWindow m (shellWidth48 m))
          s v.length b.1.1 →
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) b.1 ∈
          shellZeroSourceFailureWindow m (shellWidth48 m)
            (Fintype.card (TilingCoordinatesAt t eta.1.1.start
              eta.1.1.retained b.1)) := by
      intro b hV
      have hbS : b.1.1 ∈ eta.1.2 :=
        (away_mem_support_iff t eta.1.1.start eta.1.1.retained
          eta.1.2 b.1).1 b.2
      have hbase := boundaryLocalTime_eq_coordinateCard eta hm hk
        (fun j ↦ (q j : ℕ)) b.1 hbS
      have hpath : finitePathList (pathPrefix s v.length) =
          prefixedTilingPrefixPointPath eta.1.1.initial.1 eta.1.1.start
            (tilingInsertGapVector t eta.1.1.start eta.1.1.retained
              (fun j ↦ (q j : ℕ)))
            (prefixedTilingInsertionTerminal eta.1.1.initial t
              eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
                eta.1.1.tail) :=
        finitePathList_prefixedTilingInsertionPrefix eta.1.1.initial t
          eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
            eta.1.1.tail rfl
      have hlocal : localTime s v.length b.1.1 =
          Fintype.card (TilingCoordinatesAt t eta.1.1.start
            eta.1.1.retained b.1) +
          tilingDominoTotal t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) b.1 := by
        rw [localTime_eq_listLocalTime, hpath,
          prefixedTilingInsertedPrefix_localTime_at_dominoPoint
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ))
            (prefixedTilingInsertionTerminal eta.1.1.initial t
              eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
                eta.1.1.tail)
            b.1 b.1.1 (tilingExternalDomino_isBase t eta.1.1.start
              eta.1.1.retained b.1), hbase]
      have hwin := mem_shellZeroSourceTotalWindow.mp hV.2
      rw [hlocal] at hwin
      simp only [mem_shellZeroSourceFailureWindow]
      omega
    have hupper : ∀ b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2),
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) b.1 < upper eta.1.1 eta.1.2 m b := by
      intro b
      have hbS : b.1.1 ∈ eta.1.2 :=
        (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b.1).1 b.2
      have hbOriented : b.1.1 ∈ orientedTilingVTwoBases t o
          (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length := by
        rw [hsupport]
        exact hbS
      have hbRaw := (mem_orientedTilingVTwoBases_iff t o
        (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length b.1.1).mp
          hbOriented |>.1
      change b.1.1 ∈ (visitedTilingBases t s v.length).filter
        (tilingVTwoAt t (shellZeroSourceTotalWindow m (shellWidth48 m))
          s v.length) at hbRaw
      have hV := (Finset.mem_filter.mp hbRaw).2
      exact support.sourceUpper b _ (hfailure b hV)
    apply (tilingAwayTotalsScreen_split_iff_reconstructed t eta.1.1.start
      eta.1.1.retained (staticD eta.1.1 eta.1.2)
      (upper eta.1.1 eta.1.2 m) (sourceScreen t m cap eta.1.1 eta.1.2)
      q hupper).2
    intro b
    apply (tilingShellZeroSourceCoordinate_iff_prefixedVTwo
      eta.1.1.initial t eta.1.1.start eta.1.1.retained eta.1.1.tail
      (staticD eta.1.1 eta.1.2) (upper eta.1.1 eta.1.2 m) q
      (reconstructedTilingAwayTotalsOfCoordinates t eta.1.1.start
        eta.1.1.retained (staticD eta.1.1 eta.1.2)
        (upper eta.1.1 eta.1.2 m) q hupper) rfl b
      (boundaryLocalTime_eq_coordinateCard eta hm hk
        (fun j ↦ (q j : ℕ)) b.1
        ((away_mem_support_iff t eta.1.1.start eta.1.1.retained
          eta.1.2 b.1).1 b.2))
      (boundary_dominance_of_source eta hm hk q hq.1 hq.2 b)
      (hwindow.translate b)
      (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
        eta.1.1.retained (staticD eta.1.1 eta.1.2) q b)).2
    have hbS : b.1.1 ∈ eta.1.2 :=
      (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b.1).1 b.2
    have hbOriented : b.1.1 ∈ orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length := by
      rw [hsupport]
      exact hbS
    have hbRaw := (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s v.length b.1.1).mp
        hbOriented |>.1
    change b.1.1 ∈ (visitedTilingBases t s v.length).filter
      (tilingVTwoAt t (shellZeroSourceTotalWindow m (shellWidth48 m))
        s v.length) at hbRaw
    exact (Finset.mem_filter.mp hbRaw).2

end

end Erdos1165.TilingShellZeroSourceScreenForward
