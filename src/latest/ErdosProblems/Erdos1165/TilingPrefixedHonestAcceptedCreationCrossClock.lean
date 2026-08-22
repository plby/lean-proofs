/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedCrossClockSelectorComparison

/-!
# Cross-clock comparison with honest accepted-creation screens

The combinatorial source/replacement screen is not, by itself, a stopped
creation acceptor.  This module conjoins it with a complete creation screen
at each clock, derives both exact factorizations, and invokes the generic
cross-clock comparison only on those honest full screens.
-/

open Set

namespace Erdos1165.TilingPrefixedHonestAcceptedCreationCrossClock

open FiniteDominoProductLaw
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingPrefixedCrossClockSelectorComparison
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- One accepted-creation clock on a fixed prefixed retained carrier. -/
structure AcceptedCreationClockData
    (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) where
  stoppingTime : StepPath → ℕ
  predicate : TilingCappedCoordinates i cap → Prop
  selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop
  baseAccepts : TruncatedTotals upper → Prop
  forward : ∀ q,
    predicate q ∧ PrefixedTilingStoppingAccepted stoppingTime initial
        t x r (fun j ↦ (q j : ℕ)) tail →
      selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
        TilingAwayTotalsScreen t x r D upper baseAccepts
          ((splitTilingCoordinatesEquiv t x r D q).2)
  recover : ∀ q,
    selected ((splitTilingCoordinatesEquiv t x r D q).1) →
      TilingAwayTotalsScreen t x r D upper baseAccepts
          ((splitTilingCoordinatesEquiv t x r D q).2) →
        predicate q ∧ PrefixedTilingStoppingAccepted stoppingTime initial
          t x r (fun j ↦ (q j : ℕ)) tail

namespace AcceptedCreationClockData

variable
    {initial : List Direction} {i cap : ℕ}
    {t : DominoTiling} {x : Point} {r : TilingRetainedWord t x i}
    {tail : List Direction} {D : Finset Point}
    {upper : TilingAwayDomino t x r D → ℕ}

theorem base_factorization
    (data : AcceptedCreationClockData (cap := cap) initial t x r tail D upper)
    (q : TilingCappedCoordinates i cap) :
    data.predicate q ∧
        PrefixedTilingStoppingAccepted data.stoppingTime initial t x r
          (fun j ↦ (q j : ℕ)) tail ↔
      data.selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
        TilingAwayTotalsScreen t x r D upper data.baseAccepts
          ((splitTilingCoordinatesEquiv t x r D q).2) := by
  constructor
  · exact data.forward q
  · rintro ⟨hselected, hscreen⟩
    exact data.recover q hselected hscreen

/-- The honest source/replacement screen is the complete creation screen
conjoined with the corresponding combinatorial window. -/
def fullScreen
    (data : AcceptedCreationClockData (cap := cap) initial t x r tail D upper)
    (screen : TruncatedTotals upper → Prop) (ell : TruncatedTotals upper) :
    Prop :=
  data.baseAccepts ell ∧ screen ell

def screenedPredicate
    (data : AcceptedCreationClockData (cap := cap) initial t x r tail D upper)
    (screen : TruncatedTotals upper → Prop)
    (q : TilingCappedCoordinates i cap) : Prop :=
  data.predicate q ∧
    TilingAwayTotalsScreen t x r D upper (data.fullScreen screen)
      ((splitTilingCoordinatesEquiv t x r D q).2)

theorem screened_factorization
    (data : AcceptedCreationClockData (cap := cap) initial t x r tail D upper)
    (screen : TruncatedTotals upper → Prop)
    (q : TilingCappedCoordinates i cap) :
    data.screenedPredicate screen q ∧
        PrefixedTilingStoppingAccepted data.stoppingTime initial t x r
          (fun j ↦ (q j : ℕ)) tail ↔
      data.selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
        TilingAwayTotalsScreen t x r D upper (data.fullScreen screen)
          ((splitTilingCoordinatesEquiv t x r D q).2) := by
  constructor
  · rintro ⟨⟨hpredicate, hfull⟩, haccepted⟩
    exact ⟨(data.forward q ⟨hpredicate, haccepted⟩).1, hfull⟩
  · rintro ⟨hselected, hfull⟩
    have hbase : TilingAwayTotalsScreen t x r D upper data.baseAccepts
        ((splitTilingCoordinatesEquiv t x r D q).2) := by
      rcases hfull with ⟨ell, hell, htotal⟩
      exact ⟨ell, hell.1, htotal⟩
    have haccepted := data.recover q hselected hbase
    exact ⟨⟨haccepted.1, hfull⟩, haccepted.2⟩

end AcceptedCreationClockData

/-- Recover the old pure-window comparison without dropping creation
acceptance.  It is enough that the pure replacement screen itself forces
replacement creation.  The source full screen is automatically a subset of
the pure source screen. -/
theorem fullScreenMass_le_of_pureScreen
    {initial : List Direction} {i cap : ℕ}
    {t : DominoTiling} {x : Point} {r : TilingRetainedWord t x i}
    {tail : List Direction} {D : Finset Point}
    {upper : TilingAwayDomino t x r D → ℕ}
    (source replacement :
      AcceptedCreationClockData (cap := cap) initial t x r tail D upper)
    (sourceScreen replacementScreen : TruncatedTotals upper → Prop)
    [DecidablePred sourceScreen] [DecidablePred replacementScreen]
    [DecidablePred (source.fullScreen sourceScreen)]
    [DecidablePred (replacement.fullScreen replacementScreen)]
    (ratio : ℝ)
    (hpoint : ∀ b v,
      0 ≤ tilingAwayPointMass (cap := cap) t x r D b v)
    (hpure : screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
        sourceScreen ≤
      ratio * screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
        replacementScreen)
    (hreplacement : ∀ ell,
      replacementScreen ell → replacement.baseAccepts ell) :
    screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
        (source.fullScreen sourceScreen) ≤
      ratio * screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
        (replacement.fullScreen replacementScreen) := by
  have hsource := screenMass_mono_of_pointMass_nonneg
    (tilingAwayPointMass (cap := cap) t x r D) upper sourceScreen
      (source.fullScreen sourceScreen) hpoint (fun _ h ↦ h.2)
  have hreplacementEq : replacement.fullScreen replacementScreen =
      replacementScreen := by
    funext ell
    apply propext
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨hreplacement ell h, h⟩
  simpa only [hreplacementEq] using hsource.trans hpure

/-- Cross-clock comparison after the two pure window screens have first
been upgraded to their honest accepted-creation conjunctions.  The only
numerical input is an inequality between these full finite-product masses. -/
theorem honestScreenedGeometricMass_le_of_crossClock
    (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (source replacement :
      AcceptedCreationClockData (cap := cap) initial t x r tail D upper)
    (sourceScreen replacementScreen : TruncatedTotals upper → Prop)
    [DecidablePred source.selected] [DecidablePred replacement.selected]
    [DecidablePred (source.fullScreen sourceScreen)]
    [DecidablePred (replacement.fullScreen replacementScreen)]
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass (tilingAwayPointMass (cap := cap) t x r D) upper ell) ≠ 0)
    (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hscreen : screenMass
        (tilingAwayPointMass (cap := cap) t x r D) upper
          (replacement.fullScreen replacementScreen) ≤
      ratio * screenMass
        (tilingAwayPointMass (cap := cap) t x r D) upper
          (source.fullScreen sourceScreen))
    (hselector : prefixedTilingDistinguishedSelectorMass
        t x r D upper replacement.selected ≤
      prefixedTilingDistinguishedSelectorMass
        t x r D upper source.selected) :
    prefixedTilingStoppedAcceptedGeometricMass replacement.stoppingTime initial
        t x r cap tail (replacement.screenedPredicate replacementScreen) ≤
      ratio * prefixedTilingStoppedAcceptedGeometricMass source.stoppingTime
        initial t x r cap tail (source.screenedPredicate sourceScreen) := by
  classical
  exact prefixedTilingStoppedAcceptedGeometricMass_le_of_crossClock
    source.stoppingTime replacement.stoppingTime initial t x r tail
    (source.screenedPredicate sourceScreen)
    (replacement.screenedPredicate replacementScreen) D source.selected
    replacement.selected upper (source.fullScreen sourceScreen)
    (replacement.fullScreen replacementScreen)
    (source.screened_factorization sourceScreen)
    (replacement.screened_factorization replacementScreen)
    htotal ratio hratio hscreen hselector

end

end Erdos1165.TilingPrefixedHonestAcceptedCreationCrossClock
