/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceSingletonAccepted
import ErdosProblems.Erdos1165.HLOZSourceSlotEndpointIncrementPartition
import ErdosProblems.Erdos1165.TilingSourceSlotActualDeltaAcceptedCreation

set_option linter.style.haveILetI false

/-!
# Actual-rank product for one source-Theta slot

The accepted source-window screen is small, but its distinguished carrier
cannot be summed as an unconditional stopped atom.  For one represented
Theta base we instead expose its entire normalized coordinate law and split
that law by the literal number of newly thresholded endpoints.  Every slice
is accepted at the honest rank `k + delta`.

The only degenerate case is a completely empty fixed prefix (empty oriented
initial word, no retained block, and empty tail).  That history is the
fixed-origin history and is paid by the separate origin local-time tail.  The
theorems in this file therefore take the exact nondegeneracy statement needed
for stopped acceptance, rather than silently treating the zero vector as a
positive-time creation.
-/

namespace Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaProduct

open FiniteDominoProductLaw HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroEndpointIncrementPartition HLOZShellZeroReplacementWindows
open HLOZSourceOrientedThetaExternalSourceAccepted
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceSelectedCarrier
open HLOZSourceOrientedThetaSourceSlotAcceptedPath
open HLOZSourceOrientedThetaSourceWindowProduct
open HLOZSourceSlotEndpointIncrementPartition
open LazyDecomposition PathInsertion PreStoppingFiber SpatialInsertionFiber
open StoppedInsertion TilingCappedMarginalization TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroActualDeltaPartition
open TilingShellZeroEndpointIncrementScreen
open TilingShellZeroSourcePartition TilingSourceSlotActualDeltaAcceptedCreation
open TilingSpatialInsertionFiber TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The sole away domino on a singleton represented support. -/
theorem away_eq_of_singleton_support
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
  exact (Finset.mem_singleton.mp hc').trans
    (Finset.mem_singleton.mp hd').symm

/-- On a singleton support, an existential source failure is a failure at
the unique away coordinate. -/
theorem source_bad_at_every_away_of_singleton
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

/-- The coordinate-independent terminal used to define actual endpoint
increments. -/
def sourceActualDeltaTerminal {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t) : Option Point :=
  prefixedTilingInsertionTerminal z.initial t z.start z.retained
    (fun _ ↦ 0) z.tail

/-- The endpoint contribution of one unrestricted replacement total. -/
def sourceActualDeltaContribution
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ)
    (c : TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (v : Fin (data.upper cap c)) : ℕ :=
  prefixedShellZeroEndpointContribution z.initial.1 t z.start z.retained
    (sourceActualDeltaTerminal z)
    (supportComplementDistinguished t z.start z.retained S)
    (data.upper cap) m c v

theorem sourceActualDeltaContribution_le_two
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ)
    (c : TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (v : Fin (data.upper cap c)) :
    sourceActualDeltaContribution data cap c v ≤ 2 := by
  exact prefixedShellZeroEndpointContribution_le_two z.initial.1 t z.start
    z.retained (sourceActualDeltaTerminal z)
    (supportComplementDistinguished t z.start z.retained S)
    (data.upper cap) m c v

/-- Literal actual endpoint count, using the same canonical finite away
enumeration as the stopped tiling product. -/
def sourceActualDeltaValue
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ)
    (ell : TruncatedTotals (data.upper cap)) : ℕ :=
  @endpointIncrementOfVector
    (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (fun c ↦ Fin (data.upper cap c))
    (sourceActualDeltaContribution data cap) ell

/-- Canonical finite index type for actual endpoint increments. -/
abbrev SourceActualDeltaIndex
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (_data : Spec t o m k supportAt S z) :=
  ReplacementEndpointIncrement
    (@Fintype.card
      (TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S))
      (instFintypeTilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S))) 0

/-- One actual endpoint-increment slice of the unrestricted away law. -/
def sourceActualDeltaScreen
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ)
    (delta : SourceActualDeltaIndex data)
    (ell : TruncatedTotals (data.upper cap)) : Prop :=
  sourceActualDeltaValue data cap ell = delta

noncomputable instance instDecidablePredSourceActualDeltaScreen
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ)
    (delta : SourceActualDeltaIndex data) :
    DecidablePred (sourceActualDeltaScreen data cap delta) :=
  Classical.decPred _

/-- Normalized mass of one actual endpoint-increment slice, with the
canonical tiling-away finite enumeration fixed explicitly. -/
noncomputable def sourceActualDeltaScreenMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ)
    (delta : SourceActualDeltaIndex data) : ℝ :=
  @screenMass
    (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (data.upper cap) (sourceActualDeltaScreen data cap delta)
    (Classical.decPred _)

/-- Stopping clock at the honest actual endpoint increment. -/
def sourceActualDeltaStoppingTime
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ)
    (delta : SourceActualDeltaIndex data) :
    StepPath → ℕ :=
  truncatedLevelTime m (k + (delta : ℕ))
    (externalCoordinateCutoff z (data.coordinateCap cap))

/-- A selected source witness transports every unrestricted away total to
the creation clock indexed by its literal endpoint increment. -/
theorem externalSourceSelected_replacement_accepted
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap w externalLow externalHigh : ℕ)
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
    (qReplacement : TilingCappedCoordinates eta.1.1.retainedCount
      ((concreteFiber o m k supportAt supportData eta).coordinateCap cap))
    (hselected :
      let data := concreteFiber o m k supportAt supportData eta
      let sourceData := withExternalSourceSelected data w externalLow externalHigh
      sourceData.selected cap
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) qReplacement).1))
    (ellReplacement : TruncatedTotals
      ((concreteFiber o m k supportAt supportData eta).upper cap))
    (htotalReplacement : ∀ c,
      tilingAwayTotal t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2)
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) qReplacement).2) c = ellReplacement c) :
    let data := concreteFiber o m k supportAt supportData eta
    let delta := sourceActualDeltaValue data cap ellReplacement
    PrefixedTilingStoppingAccepted
      (truncatedLevelTime m (k + delta)
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qReplacement j : ℕ)) eta.1.1.tail.1 := by
  classical
  dsimp only
  let data := concreteFiber o m k supportAt supportData eta
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  change externalSourceSelected data w externalLow externalHigh cap
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2) qReplacement).1) at hselected
  rcases hselected with ⟨aSource, ellSource, hatomSource, hacceptedSource,
    hbadSource, htotalSourceAway⟩
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  let qSource := (splitTilingCoordinatesEquiv t eta.1.1.start
      eta.1.1.retained D).symm
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
      qReplacement).1, aSource)
  let bext : TilingExternalDomino t eta.1.1.start eta.1.1.retained := ⟨b, hb⟩
  have hdist :
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
        qSource).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
        qReplacement).1 := by
    simp only [qSource, Equiv.apply_symm_apply]
  have hterminal : prefixedTilingInsertionTerminal eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
        eta.1.1.tail = sourceActualDeltaTerminal eta.1.1 := by
    apply prefixedTilingInsertionTerminal_eq_of_coordinates
      eta.1.1.initial t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qSource j : ℕ)) (fun _ ↦ 0) eta.1.1.tail rfl
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
  have hbase : ∀ c : TilingAwayDomino t eta.1.1.start eta.1.1.retained D,
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained
          (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
            eta.1.1.retained (fun j ↦ (qSource j : ℕ)) eta.1.1.tail) c.1.1 =
        Fintype.card (TilingCoordinatesAt t eta.1.1.start
          eta.1.1.retained c.1) := by
    intro c
    have hcS := (away_mem_support_iff t eta.1.1.start eta.1.1.retained
      eta.1.2 c.1).1 c.2
    have hcb : c.1.1 = b := by
      rw [hS, Finset.mem_singleton] at hcS
      exact hcS
    have hccompat : OrientationCompatible o c.1.1 := by
      simpa only [hcb] using hcompat
    exact prefixedBoundaryLocalTime_eq_coordinateCard_external eta hm hk
      (fun j ↦ (qSource j : ℕ)) c.1 hccompat
  have hdominance : ∀ c : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained D,
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained
          (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
            eta.1.1.retained (fun j ↦ (qSource j : ℕ)) eta.1.1.tail)
          (tilingPartner t c.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained
          (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
            eta.1.1.retained (fun j ↦ (qSource j : ℕ)) eta.1.1.tail) c.1.1 := by
    intro c
    have hcS := (away_mem_support_iff t eta.1.1.start eta.1.1.retained
      eta.1.2 c.1).1 c.2
    have hcb : c.1.1 = b := by
      rw [hS, Finset.mem_singleton] at hcS
      exact hcS
    simpa only [hcb] using hdom qSource
  have hsource : ∀ c : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained D,
      tilingShellZeroSourceCoordinate (cap := data.coordinateCap cap)
        (m := m) (w := w) t eta.1.1.start eta.1.1.retained D
        (data.upper cap) c (ellSource c) := by
    intro c
    exact (source_bad_at_every_away_of_singleton data hS w externalLow
      externalHigh cap ellSource hbadSource c).1
  have htotalSource : ∀ c : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained D,
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qSource j : ℕ)) c.1 = (ellSource c : ℕ) := by
    intro c
    calc
      _ = tilingAwayTotal t eta.1.1.start eta.1.1.retained D
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
            qSource).2) c :=
        (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
          eta.1.1.retained D qSource c).symm
      _ = _ := by
        simpa only [qSource, Equiv.apply_symm_apply] using htotalSourceAway c
  have htotalReplacement' : ∀ c : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained D,
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qReplacement j : ℕ)) c.1 = (ellReplacement c : ℕ) := by
    intro c
    exact (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
      eta.1.1.retained D qReplacement c).symm.trans
        (htotalReplacement c)
  have hposSource : 0 < (prefixedTilingInsertionPrefixList
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qSource j : ℕ)) eta.1.1.tail.1).length := by
    unfold OrientedTilingTypedExternalWordCode.start
    rw [prefixedTilingInsertionPrefixList_length]
    omega
  have hposReplacement : 0 < (prefixedTilingInsertionPrefixList
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qReplacement j : ℕ)) eta.1.1.tail.1).length := by
    unfold OrientedTilingTypedExternalWordCode.start
    rw [prefixedTilingInsertionPrefixList_length]
    omega
  let dummy : TilingCreationFavoriteData := ((∅, ∅),
    (eta.1.1.start, eta.1.1.start))
  have hltSource : (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
      eta.1.1.tail.1).length <
        externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) qSource
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hltReplacement : (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (qReplacement j : ℕ))
      eta.1.1.tail.1).length <
        externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) qReplacement
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hacceptedSource' : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qSource j : ℕ)) eta.1.1.tail.1 := by
    exact hacceptedSource
  have hresult := prefixedTilingStoppingAccepted_at_arbitraryEndpointIncrement
    eta.1.1.initial t eta.1.1.start eta.1.1.retained eta.1.1.tail D
    (data.upper cap) k
    (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)) (by omega) hk
    qSource qReplacement ellSource ellReplacement rfl hdist hbase hdominance
    hsource htotalSource htotalReplacement' hposSource hposReplacement
    hltSource hltReplacement hacceptedSource'
  unfold sourceActualDeltaValue sourceActualDeltaContribution
  simpa only [D, data, hterminal] using hresult

/-- Coordinate predicate for one honest actual-increment rank.  The
distinguished projection is the accepted source selector; the away vector is
otherwise unrestricted except for its literal endpoint count. -/
def sourceActualDeltaPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (delta : SourceActualDeltaIndex data)
    (q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap)) :
    Prop :=
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  sourceData.selected cap
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).1) ∧
    TilingAwayTotalsScreen t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
      (data.upper cap) (sourceActualDeltaScreen data cap delta)
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).2)

/-- Exact factorization of one actual-increment stopped rank piece. -/
theorem sourceActualDeltaPredicate_factorization
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap w externalLow externalHigh : ℕ)
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
    (delta : SourceActualDeltaIndex
      (concreteFiber o m k supportAt supportData eta))
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((concreteFiber o m k supportAt supportData eta).coordinateCap cap)) :
    let data := concreteFiber o m k supportAt supportData eta
    sourceActualDeltaPredicate data w externalLow externalHigh cap delta q ∧
        PrefixedTilingStoppingAccepted
          (sourceActualDeltaStoppingTime data cap delta)
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 ↔
      (withExternalSourceSelected data w externalLow externalHigh).selected cap
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2) q).1) ∧
        TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) (data.upper cap)
          (sourceActualDeltaScreen data cap delta)
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2) q).2) := by
  classical
  dsimp only
  let data := concreteFiber o m k supportAt supportData eta
  constructor
  · exact fun h ↦ h.1
  · rintro ⟨hselected, ell, hdelta, htotal⟩
    refine ⟨⟨hselected, ⟨ell, hdelta, htotal⟩⟩, ?_⟩
    have haccepted := externalSourceSelected_replacement_accepted supportData
      eta hm hk hfixedPos cap w externalLow externalHigh b hS hb hcompat q₀
      window hVTwo q hselected ell htotal
    dsimp only at haccepted
    change sourceActualDeltaValue data cap ell = (delta : ℕ) at hdelta
    unfold sourceActualDeltaStoppingTime
    rw [hdelta] at haccepted
    exact haccepted

/-- The geometric mass of one actual-increment rank piece is its normalized
increment-slice mass times the exact accepted-source distinguished carrier. -/
theorem sourceActualDeltaStoppedGeometricMass_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap w externalLow externalHigh : ℕ)
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
    (delta : SourceActualDeltaIndex
      (concreteFiber o m k supportAt supportData eta)) :
    let data := concreteFiber o m k supportAt supportData eta
    prefixedTilingStoppedAcceptedGeometricMass
        (sourceActualDeltaStoppingTime data cap delta)
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (data.coordinateCap cap) eta.1.1.tail.1
        (sourceActualDeltaPredicate data w externalLow externalHigh cap delta) =
      sourceActualDeltaScreenMass data cap delta *
        externalAcceptedThetaCarrier
          (withExternalSourceSelected data w externalLow externalHigh) cap := by
  classical
  dsimp only
  let data := concreteFiber o m k supportAt supportData eta
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  let D := supportComplementDistinguished t eta.1.1.start eta.1.1.retained
    eta.1.2
  letI : Fintype (TilingAwayDomino t eta.1.1.start eta.1.1.retained D) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  letI : Fintype (TilingDistinguishedDomino t eta.1.1.start
      eta.1.1.retained D) :=
    instFintypeTilingDistinguishedDomino t eta.1.1.start eta.1.1.retained D
  have h :=
    @prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
    (sourceActualDeltaStoppingTime data cap delta) eta.1.1.initial.1
    eta.1.1.retainedCount (data.coordinateCap cap) t eta.1.1.start
    eta.1.1.retained eta.1.1.tail.1
    (sourceActualDeltaPredicate data w externalLow externalHigh cap delta)
    (Classical.decPred _) D (sourceData.selected cap) (Classical.decPred _)
    (data.upper cap) (sourceActualDeltaScreen data cap delta)
    (Classical.decPred _)
    (sourceActualDeltaPredicate_factorization supportData eta hm hk hfixedPos
      cap w externalLow externalHigh b hS hb hcompat q₀ window hVTwo delta)
    (by
      apply ne_of_gt
      apply Finset.sum_pos'
      · intro ell _hell
        exact Finset.prod_nonneg fun c _ ↦
          tilingAwayExactTotalMass_nonneg t eta.1.1.start eta.1.1.retained D
            c (ell c)
      · let zero : TruncatedTotals (data.upper cap) :=
          fun c ↦ ⟨0, data.upper_pos cap c⟩
        refine ⟨zero, Finset.mem_univ _, ?_⟩
        unfold jointMass
        apply Finset.prod_pos
        intro c _hc
        exact tilingAwayExactTotalMass_zero_pos t eta.1.1.start
          eta.1.1.retained D c)
  unfold sourceActualDeltaScreenMass externalAcceptedThetaCarrier
  convert h using 1
  · simp only [data, sourceData, D, tilingDistinguishedAssignmentMass]
    congr 1

/-- The unrestricted accepted-source carrier is exactly the finite sum of
its honest actual-rank pieces. -/
theorem sum_sourceActualDeltaStoppedGeometricMass_eq_carrier
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap w externalLow externalHigh : ℕ)
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
      tilingVTwoAt t window s v.length b) :
    let data := concreteFiber o m k supportAt supportData eta
    (∑ delta : SourceActualDeltaIndex data,
      prefixedTilingStoppedAcceptedGeometricMass
        (sourceActualDeltaStoppingTime data cap delta)
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (data.coordinateCap cap) eta.1.1.tail.1
        (sourceActualDeltaPredicate data w externalLow externalHigh cap delta)) =
      externalAcceptedThetaCarrier
        (withExternalSourceSelected data w externalLow externalHigh) cap := by
  classical
  dsimp only
  let data := concreteFiber o m k supportAt supportData eta
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  let D := supportComplementDistinguished t eta.1.1.start eta.1.1.retained
    eta.1.2
  have hpiece : ∀ delta : SourceActualDeltaIndex data,
      prefixedTilingStoppedAcceptedGeometricMass
          (sourceActualDeltaStoppingTime data cap delta)
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (data.coordinateCap cap) eta.1.1.tail.1
          (sourceActualDeltaPredicate data w externalLow externalHigh cap delta) =
        sourceActualDeltaScreenMass data cap delta *
          externalAcceptedThetaCarrier sourceData cap := by
    intro delta
    exact sourceActualDeltaStoppedGeometricMass_eq supportData eta hm hk
      hfixedPos cap w externalLow externalHigh b hS hb hcompat q₀ window
      hVTwo delta
  have hscreen : (∑ delta : SourceActualDeltaIndex data,
      sourceActualDeltaScreenMass data cap delta) = 1 := by
    have hpartition := @sum_screenMass_vectorAtEndpointIncrement_eq_one
        (TilingAwayDomino t eta.1.1.start eta.1.1.retained D)
        (instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D)
        (fun a b ↦ Subtype.instDecidableEq a b)
        (data.upper cap)
        (tilingAwayPointMass (cap := data.coordinateCap cap) t
          eta.1.1.start eta.1.1.retained D)
        (sourceActualDeltaContribution data cap)
        (sourceActualDeltaContribution_le_two data cap)
        (externalTheta_coordinate_sum_eq_one data cap)
    rw [← hpartition]
    apply Finset.sum_congr rfl
    intro delta _hdelta
    unfold sourceActualDeltaScreenMass screenMass
    apply Finset.sum_congr rfl
    intro ell _hell
    apply if_congr
    · rfl
    · rfl
    · rfl
  change (∑ delta : SourceActualDeltaIndex data,
      prefixedTilingStoppedAcceptedGeometricMass
        (sourceActualDeltaStoppingTime data cap delta)
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (data.coordinateCap cap) eta.1.1.tail.1
        (sourceActualDeltaPredicate data w externalLow externalHigh cap delta)) =
    externalAcceptedThetaCarrier sourceData cap
  calc
    _ = ∑ delta : SourceActualDeltaIndex data,
        sourceActualDeltaScreenMass data cap delta *
          externalAcceptedThetaCarrier sourceData cap := by
      apply Finset.sum_congr rfl
      intro delta _hdelta
      exact hpiece delta
    _ = externalAcceptedThetaCarrier sourceData cap := by
      rw [← Finset.sum_mul, hscreen, one_mul]

end

end Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaProduct
