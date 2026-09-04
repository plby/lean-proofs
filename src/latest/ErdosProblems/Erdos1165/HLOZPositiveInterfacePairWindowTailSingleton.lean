/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWindowTail
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWindowTailProduct
import ErdosProblems.Erdos1165.HLOZPrefixedStoppedProductUpperFactorization
import ErdosProblems.Erdos1165.HLOZActualDeltaSelectedProduct
import ErdosProblems.Erdos1165.TilingOrientedExternalStaticDStoppedCoordinate

/-!
# A code-visible singleton carrier for a failed pair-window ratio

The exact adjacent-pair support is not determined by the retained external
word.  For the exceptional-window payment we instead expose one represented
domino at a time.  The resulting singleton selector is determined by the
external code, so its honest raised-rank atoms can later be summed without
remembering the full pair support.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Erdos1165.HLOZPositiveInterfacePairWindowTailSingleton

open FiniteDominoProductLaw
open HLOZActualDeltaSelectedProduct
open HLOZFiniteProductCoordinateUnion
open HLOZPathEvents
open HLOZPositiveInterfacePairActualDeltaCapBound
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedScreen
open HLOZPositiveInterfacePairWindowTail
open HLOZPositiveInterfacePairWindowTailProduct
open HLOZPrefixedStoppedProductUpperFactorization
open HLOZProposition48Candidates
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PathInsertion PreStoppingFiber StoppedInsertion
open ScreeningInstantiation
open TilingCappedMarginalization
open TilingBroadSourceSlotActualDeltaAcceptedCreation
open TilingDistinguishedTraceInvariant
open TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedExternalStaticDStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedInsertedLocalTime
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The singleton `{b}` when `b` is represented by the retained external
word, and the empty set otherwise. -/
def representedSingletonSupportOfCode (t : DominoTiling) (b : Point)
    (z : OrientedTilingTypedExternalWordCode t) : Finset Point :=
  if b ∈ tilingExternalDominoBases t z.start z.retained then {b} else ∅

def representedSingletonSupportAt (t : DominoTiling) (o : Orientation)
    (b : Point) (s : WalkPath) (n : ℕ) : Finset Point :=
  representedSingletonSupportOfCode t b
    (fixedOrientedTypedExternalWordCode t o n s)

theorem representedSingletonSupportData
    (t : DominoTiling) (o : Orientation) (m k : ℕ) (b : Point) :
    OrientedAllCreationSupportSelectorData t o m k
      (representedSingletonSupportAt t o b) := by
  constructor
  · exact measurable_natIndexed (creationTimeNat m k)
      (measurable_creationTimeNat m k)
      (fun n s ↦ representedSingletonSupportAt t o b s n)
      (fun n ↦ measurable_of_pathPrefix_invariant n _ (by
        intro s s' hp
        unfold representedSingletonSupportAt
        rw [fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp]))
  · intro s s' n hp
    unfold representedSingletonSupportAt
    rw [fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp]
  · intro s n _hvalid
    unfold representedSingletonSupportAt representedSingletonSupportOfCode
    split
    next hb => simpa only [Finset.singleton_subset_iff] using hb
    next _ => exact Finset.empty_subset _

/-- A coarse external word together with one represented base gives a
nonempty singleton-supported creation history. -/
noncomputable def singletonSupportedIndex
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : TilingOrientedExternalStaticDStoppedCoordinate.SupportedIndex
      t o m k)
    (b : Point)
    (hb : b ∈ tilingExternalDominoBases t eta.1.start eta.1.retained) :
    TilingOrientedExternalAllCreationStoppedCoordinate.SupportedIndex
      t o m k (representedSingletonSupportAt t o b) := by
  refine ⟨⟨eta.1, {b}⟩, ?_⟩
  rcases eta.2 with ⟨s, hs⟩
  rw [orientedExternalOnlyCreationTraceAtom] at hs
  rw [orientedExternalAllCreationSupportTraceAtom_eq]
  refine ⟨s, hs.1, hs.2.1, hs.2.2, ?_⟩
  unfold representedSingletonSupportAt representedSingletonSupportOfCode
  rw [hs.2.2, if_pos hb]

/-- The concrete singleton stopped fibre attached to a coarse code and one
represented external domino. -/
noncomputable def singletonFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : TilingOrientedExternalStaticDStoppedCoordinate.SupportedIndex
      t o m k)
    (b : Point)
    (hb : b ∈ tilingExternalDominoBases t eta.1.start eta.1.retained) :=
  concreteFiber o m k (representedSingletonSupportAt t o b)
    (representedSingletonSupportData t o m k b)
    (singletonSupportedIndex eta b hb)

@[simp] theorem singletonSupportedIndex_code
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : TilingOrientedExternalStaticDStoppedCoordinate.SupportedIndex
      t o m k)
    (b : Point)
    (hb : b ∈ tilingExternalDominoBases t eta.1.start eta.1.retained) :
    (singletonSupportedIndex eta b hb).1.1 = eta.1 := rfl

@[simp] theorem singletonSupportedIndex_support
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : TilingOrientedExternalStaticDStoppedCoordinate.SupportedIndex
      t o m k)
    (b : Point)
    (hb : b ∈ tilingExternalDominoBases t eta.1.start eta.1.retained) :
    (singletonSupportedIndex eta b hb).1.2 = {b} := rfl

/-- The unique away coordinate of the singleton fibre. -/
noncomputable def singletonCoordinate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : TilingOrientedExternalStaticDStoppedCoordinate.SupportedIndex
      t o m k)
    (b : Point)
    (hb : b ∈ tilingExternalDominoBases t eta.1.start eta.1.retained) :
    TilingAwayDomino t eta.1.start eta.1.retained
      (supportComplementDistinguished t eta.1.start eta.1.retained {b}) :=
  supportAwayChosen t eta.1.start eta.1.retained {b}
    (by simpa only [Finset.singleton_subset_iff] using hb) b (by simp)

@[simp] theorem singletonCoordinate_base
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : TilingOrientedExternalStaticDStoppedCoordinate.SupportedIndex
      t o m k)
    (b : Point)
    (hb : b ∈ tilingExternalDominoBases t eta.1.start eta.1.retained) :
    (singletonCoordinate eta b hb).1.1 = b := rfl

/-- Forget the exact adjacent-pair support while retaining the external word. -/
noncomputable def pairCoarseIndex
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) :
    TilingOrientedExternalStaticDStoppedCoordinate.SupportedIndex t o m k := by
  refine ⟨eta.1.1, ?_⟩
  rcases eta.2 with ⟨s, hs⟩
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
  exact ⟨s, hs.1, hs.2.1, hs.2.2.1⟩

@[simp] theorem pairCoarseIndex_code
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) :
    (pairCoarseIndex eta).1 = eta.1.1 := rfl

/-- The singleton stopped fibre obtained from one coordinate of an exact
adjacent-pair history. -/
noncomputable def singletonPairFiber
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) :=
  singletonFiber (pairCoarseIndex eta) b.1.1 b.1.2

/-- The distinguished singleton coordinate corresponding to the offending
coordinate in the original pair fibre. -/
noncomputable def singletonPairCoordinate
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) :
    TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        ({b.1.1} : Finset Point)) :=
  singletonCoordinate (pairCoarseIndex eta) b.1.1 b.1.2

@[simp] theorem singletonPairCoordinate_base
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) :
    (singletonPairCoordinate eta b).1.1 = b.1.1 := rfl

/-- Prefix-correct safe totals on the exposed singleton coordinate. -/
noncomputable def singletonPairBaseWindow
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) (_cap : ℕ)
    (c : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        ({b.1.1} : Finset Point))) : Finset ℕ :=
  Finset.range (m - prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1
    eta.1.1.start eta.1.1.retained (sourceActualDeltaTerminal eta.1.1) c.1)

def singletonPairBaseProp
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) (cap : ℕ)
    (ell : TruncatedTotals ((singletonPairFiber eta b).upper cap)) : Prop :=
  ∀ c, (ell c : ℕ) ∈ singletonPairBaseWindow eta b cap c

/-- Distinguished assignments admitting one accepted, prefix-safe source
completion on the singleton coordinate. -/
def singletonPairSelected
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) (cap : ℕ)
    (d : TilingDistinguishedCoordinates
      (cap := (singletonPairFiber eta b).coordinateCap cap)
      t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point))) : Prop :=
  ∃ a ell,
    let data := singletonPairFiber eta b
    let q := (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        ({b.1.1} : Finset Point))).symm (d, a)
    PrefixedTilingStoppingAccepted (data.stoppingTime cap)
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 ∧
      singletonPairBaseProp eta b cap ell ∧
      ∀ c, tilingAwayTotal t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point)) a c = ell c

/-- The offending adjacent-window tail on the exposed singleton coordinate. -/
def singletonPairWindowScreen
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) (cap : ℕ)
    (ell : TruncatedTotals ((singletonPairFiber eta b).upper cap)) : Prop :=
  (ell (singletonPairCoordinate eta b) : ℕ) ∈
    positiveInterfacePairWindow m (shellWidth48 m)
      (Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell

/-- Normalized product mass of the offending singleton tail. -/
noncomputable def singletonPairWindowScreenMass
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) (cap : ℕ) : ℝ :=
  let data := singletonPairFiber eta b
  @screenMass
    (TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        ({b.1.1} : Finset Point)))
    (instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        ({b.1.1} : Finset Point)))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t eta.1.1.start
      eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        ({b.1.1} : Finset Point)))
    (data.upper cap)
    (fun ell ↦ (ell (singletonPairCoordinate eta b) : ℕ) ∈
      positiveInterfacePairWindow m (shellWidth48 m)
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell)
    (fun ell ↦ Finset.decidableMem
      (ell (singletonPairCoordinate eta b) : ℕ)
      (positiveInterfacePairWindow m (shellWidth48 m)
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell))

/-- The normalized singleton screen is exactly the offending-coordinate
tail and is at most twice its raw negative-binomial window mass. -/
theorem singletonPairWindowScreenMass_le_two_mul_windowMass
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (cap : ℕ) (b : PositiveInterfaceExternalPairCoordinate eta) :
    singletonPairWindowScreenMass eta b cap ≤
      2 * SmallWindow.windowMass
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
        (positiveInterfacePairWindow m (shellWidth48 m)
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          shell) := by
  classical
  let data := singletonPairFiber eta b
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained ({b.1.1} : Finset Point)
  let singletonFintype : Fintype
      (TilingAwayDomino t eta.1.1.start eta.1.1.retained D) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  let c := singletonPairCoordinate eta b
  let pointMass := tilingAwayPointMass (cap := data.coordinateCap cap) t
    eta.1.1.start eta.1.1.retained D
  let upper := data.upper cap
  let bad : ∀ d, Fin (upper d) → Prop := fun _ v ↦
    (v : ℕ) ∈ positiveInterfacePairWindow m (shellWidth48 m)
      (Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell
  let badDec : ∀ d, DecidablePred (bad d) := fun _ v ↦
    Finset.decidableMem (v : ℕ)
      (positiveInterfacePairWindow m (shellWidth48 m)
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell)
  have hsum : ∀ d, (∑ v : Fin (upper d),
      coordinateMass pointMass upper d v) = 1 := by
    intro d
    exact externalTheta_coordinate_sum_eq_one data cap d
  have hsingle := screenMass_single_coordinate_eq pointMass upper bad hsum c
  have hscreen : singletonPairWindowScreenMass eta b cap =
      ∑ v : Fin (upper c),
        if (v : ℕ) ∈ positiveInterfacePairWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell
        then coordinateMass pointMass upper c v else 0 := by
    unfold singletonPairWindowScreenMass
    simpa only [data, D, singletonFintype, c, pointMass, upper, bad,
      badDec] using hsingle
  rw [hscreen]
  have htail :=
    sum_positiveInterfacePairWindow_coordinateMass_le_two_mul_windowMass
      eta cap b
  convert htail using 1 <;>
    simp only [data, D, c, pointMass, upper, singletonPairFiber,
      singletonFiber, singletonPairCoordinate, singletonCoordinate,
      pairCoarseIndex, singletonSupportedIndex, coordinateMass,
      tilingAwayPointMass, tilingAwayExactTotalMass,
      TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber] <;>
    rfl

/-- Failure of the adjacent-row comparison supplies the sharp exponential
bound for the normalized singleton screen. -/
theorem singletonPairWindowScreenMass_le_of_not_windowRatio
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (cap : ℕ) (b : PositiveInterfaceExternalPairCoordinate eta)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hthick : m / 2 ≤ Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
    (him : Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) ≤ m)
    (hfit : (shell + 2) * shellWidth48 m ≤ m)
    (hwidthDeviation :
      24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hbad : ¬ SmallWindow.windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (HLOZPositiveInterfacePhysicalWindowRatio.acceptedPhysicalDeficitFailureWindow
            m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            (shell + 1)) ≤
        positiveInterfaceRatioConstant * SmallWindow.windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (HLOZPositiveInterfacePhysicalWindowRatio.acceptedPhysicalDeficitFailureWindow
            m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            shell)) :
    singletonPairWindowScreenMass eta b cap ≤
      2 * Real.exp (-17 * balanceRateScale m) := by
  calc
    _ ≤ 2 * SmallWindow.windowMass
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
        (positiveInterfacePairWindow m (shellWidth48 m)
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          shell) := singletonPairWindowScreenMass_le_two_mul_windowMass
            eta cap b
    _ ≤ 2 * Real.exp (-17 * balanceRateScale m) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact acceptedPhysicalPairWindowMass_le_of_not_windowRatio
        harithmetic hwidthFour hthick him hfit hwidthDeviation
          hdeviationLevel hbad

/-- A prefix-safe accepted singleton source transports every unrestricted
replacement total to its literal endpoint-increment clock. -/
theorem singletonPairSelected_replacement_accepted
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ)
    (qReplacement : TilingCappedCoordinates eta.1.1.retainedCount
      ((singletonPairFiber eta b).coordinateCap cap))
    (hselected : singletonPairSelected eta b cap
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point)) qReplacement).1))
    (ellReplacement : TruncatedTotals ((singletonPairFiber eta b).upper cap))
    (htotalReplacement : ∀ c,
      tilingAwayTotal t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point))
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            ({b.1.1} : Finset Point)) qReplacement).2) c = ellReplacement c) :
    let data := singletonPairFiber eta b
    let delta := sourceActualDeltaValue data cap ellReplacement
    PrefixedTilingStoppingAccepted
      (truncatedLevelTime m (k + delta)
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qReplacement j : ℕ)) eta.1.1.tail.1 := by
  classical
  dsimp only
  let data := singletonPairFiber eta b
  change singletonPairSelected eta b cap
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        ({b.1.1} : Finset Point)) qReplacement).1) at hselected
  rcases hselected with ⟨aSource, ellSource, hacceptedSource,
    hbaseSource, htotalSourceAway⟩
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained ({b.1.1} : Finset Point)
  let qSource := (splitTilingCoordinatesEquiv t eta.1.1.start
      eta.1.1.retained D).symm
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
      qReplacement).1, aSource)
  have hdist :
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
        qSource).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
        qReplacement).1 := by
    simp only [qSource, Equiv.apply_symm_apply]
  have hterminal : prefixedTilingInsertionTerminal eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
        eta.1.1.tail = sourceActualDeltaTerminal eta.1.1 := by
    exact prefixedTilingInsertionTerminal_eq_of_coordinates eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
      (fun _ ↦ 0) eta.1.1.tail rfl
  have hsourceBelow : ∀ c : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained D,
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained
          (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
            eta.1.1.retained (fun j ↦ (qSource j : ℕ)) eta.1.1.tail)
          c.1.1 + (ellSource c : ℕ) < m ∧
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained
          (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
            eta.1.1.retained (fun j ↦ (qSource j : ℕ)) eta.1.1.tail)
          (tilingPartner t c.1.1) + (ellSource c : ℕ) < m := by
    intro c
    have hc := hbaseSource c
    unfold singletonPairBaseWindow at hc
    rw [Finset.mem_range] at hc
    rw [hterminal]
    unfold prefixedTilingFixedBoundaryDominoMax at hc
    constructor <;> omega
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
      eta.1.1.retained D qReplacement c).symm.trans (htotalReplacement c)
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
  let dummy : TilingCreationFavoriteData :=
    ((∅, ∅), (eta.1.1.start, eta.1.1.start))
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
  have hresult := prefixedTilingStoppingAccepted_at_broadEndpointIncrement
    eta.1.1.initial t eta.1.1.start eta.1.1.retained eta.1.1.tail D
    (data.upper cap) k
    (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)) hm hk
    qSource qReplacement ellSource ellReplacement rfl hdist hsourceBelow
    htotalSource htotalReplacement' hposSource hposReplacement hltSource
    hltReplacement hacceptedSource
  unfold sourceActualDeltaValue sourceActualDeltaContribution
  simp only [D, data, hterminal, singletonPairFiber, singletonFiber,
    pairCoarseIndex, singletonSupportedIndex] at hresult
  simp only [singletonPairFiber, singletonFiber, pairCoarseIndex,
    singletonSupportedIndex]
  exact hresult

/-- Generic selected-factorization acceptance for one singleton actual-delta
slice. -/
theorem singletonPair_actualDeltaAccepted
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (delta : SourceActualDeltaIndex (singletonPairFiber eta b))
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((singletonPairFiber eta b).coordinateCap cap))
    (hselected : singletonPairSelected eta b cap
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point)) q).1))
    (hscreen : TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        ({b.1.1} : Finset Point)) ((singletonPairFiber eta b).upper cap)
      (sourceActualDeltaScreen (singletonPairFiber eta b) cap delta)
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point)) q).2)) :
    PrefixedTilingStoppingAccepted
      (sourceActualDeltaStoppingTime (singletonPairFiber eta b) cap delta)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 := by
  rcases hscreen with ⟨ell, hdelta, htotal⟩
  have h := singletonPairSelected_replacement_accepted eta b hm hk hfixedPos
    cap q hselected ell htotal
  dsimp only at h
  unfold sourceActualDeltaStoppingTime
  rw [hdelta] at h
  exact h

/-- The exact pair source predicate implies a one-coordinate factorization on
the offending singleton.  No reverse implication is needed for the upper
bound. -/
theorem positiveInterfaceExternalPairSourcePredicate_forward_singleton
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap))
    (hq : positiveInterfaceExternalPairSourcePredicate eta cap threshold bound q ∧
      PrefixedTilingStoppingAccepted
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1
            ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) eta.1.1.tail.1) :
    singletonPairSelected eta b cap
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            ({b.1.1} : Finset Point)) q).1) ∧
      TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point)) ((singletonPairFiber eta b).upper cap)
        (singletonPairWindowScreen eta b cap)
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            ({b.1.1} : Finset Point)) q).2) := by
  classical
  let DPair := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  let pairFintype : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained DPair
  rcases hq.1.2 with ⟨ellPair, hscreenPair, htotalPair⟩
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained ({b.1.1} : Finset Point)
  let c := singletonPairCoordinate eta b
  let a := (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).2
  let ell : TruncatedTotals ((singletonPairFiber eta b).upper cap) :=
    fun d ↦ ⟨(ellPair b : ℕ), by
      have hdc : d = c := away_eq_of_singleton_support rfl d c
      subst d
      simpa only [c, singletonPairCoordinate, singletonCoordinate,
        singletonPairFiber, singletonFiber, pairCoarseIndex,
        singletonSupportedIndex,
        TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber] using
          (ellPair b).isLt⟩
  have hbase : singletonPairBaseProp eta b cap ell := by
    intro d
    have hdc : d = c := away_eq_of_singleton_support rfl d c
    subst d
    have hcb : c.1 = b.1 := by
      apply Subtype.ext
      exact singletonPairCoordinate_base eta b
    have hb := hscreenPair.1 b
    change (ellPair b : ℕ) ∈ Finset.range
      (m - prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1
        eta.1.1.start eta.1.1.retained (sourceActualDeltaTerminal eta.1.1) c.1)
    rw [hcb]
    simpa only [positiveInterfaceExternalPairBaseWindow,
      positiveInterfaceExternalPairTerminal, sourceActualDeltaTerminal] using hb
  have htotal : ∀ d, tilingAwayTotal t eta.1.1.start eta.1.1.retained D a d =
      ell d := by
    intro d
    have hdc : d = c := away_eq_of_singleton_support rfl d c
    subst d
    calc
      tilingAwayTotal t eta.1.1.start eta.1.1.retained D a c =
          tilingDominoTotal t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) c.1 :=
        tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
          eta.1.1.retained D q c
      _ = tilingDominoTotal t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) b.1 := by rfl
      _ = tilingAwayTotal t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2)
            ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
              (supportComplementDistinguished t eta.1.1.start
                eta.1.1.retained eta.1.2) q).2) b :=
        (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
          eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start
            eta.1.1.retained eta.1.2) q b).symm
      _ = (ellPair b : ℕ) := htotalPair b
      _ = ell c := rfl
  have hwindow : singletonPairWindowScreen eta b cap ell := by
    have hbSupport : b ∈ HeterogeneousProductTail.pairSupport
        (positiveInterfaceExternalPairUpper eta cap)
        (positiveInterfaceExternalPairLower eta cap) ellPair := by
      exact Eq.mpr
        (congrArg (fun S ↦ b ∈ S) hscreenPair.2.2)
        (Finset.mem_univ b)
    simp only [HeterogeneousProductTail.pairSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] at hbSupport
    unfold singletonPairWindowScreen positiveInterfacePairWindow
    rw [Finset.mem_union]
    rcases hbSupport with hbUpper | hbLower
    · exact Or.inr hbUpper.1
    · exact Or.inl hbLower
  have hqReassemble :
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D).symm
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).1,
          a) = q := by
    dsimp only [a]
    exact Equiv.symm_apply_apply _ q
  constructor
  · unfold singletonPairSelected
    refine ⟨a, ell, ?_⟩
    dsimp only
    have hqValues :
        (fun j ↦
          (((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D).symm
            ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).1,
              a)) j : ℕ)) = fun j ↦ (q j : ℕ) := by
      funext j
      rw [hqReassemble]
    have htriple :
        PrefixedTilingStoppingAccepted ((singletonPairFiber eta b).stoppingTime cap)
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (fun j ↦
            (((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D).symm
              ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).1,
                a)) j : ℕ)) eta.1.1.tail.1 ∧
        singletonPairBaseProp eta b cap ell ∧
        ∀ d, tilingAwayTotal t eta.1.1.start eta.1.1.retained D a d = ell d := by
      rw [hqValues]
      exact ⟨by
        simpa only [singletonPairFiber, singletonFiber, pairCoarseIndex,
          singletonSupportedIndex,
          TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber]
          using hq.2, hbase, htotal⟩
    exact htriple
  · exact ⟨ell, hwindow, htotal⟩

/-- One offending coordinate pays for the exact pair source mass, while the
remaining distinguished coordinates are retained in the singleton accepted
carrier. -/
theorem positiveInterfaceExternalPairSourceStoppedGeometricMass_le_singleton
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ) :
    let pairData := PositiveInterfaceExternalPairFiber eta
    let data := singletonPairFiber eta b
    prefixedTilingStoppedAcceptedGeometricMass
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (pairData.coordinateCap cap) eta.1.1.tail.1
        (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound) ≤
      singletonPairWindowScreenMass eta b cap *
        externalAcceptedThetaCarrier
          (withSelected data (singletonPairSelected eta b)) cap := by
  classical
  dsimp only
  let pairData := PositiveInterfaceExternalPairFiber eta
  let data := singletonPairFiber eta b
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained ({b.1.1} : Finset Point)
  let : Fintype (TilingAwayDomino t eta.1.1.start eta.1.1.retained D) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  let : Fintype (TilingDistinguishedDomino t eta.1.1.start
      eta.1.1.retained D) :=
    instFintypeTilingDistinguishedDomino t eta.1.1.start eta.1.1.retained D
  have h :=
    @prefixedTilingStoppedAcceptedGeometricMass_le_screenMass_mul_distinguishedBase
      (truncatedLevelTime m k
        (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
      eta.1.1.initial.1 eta.1.1.retainedCount (pairData.coordinateCap cap) t
      eta.1.1.start eta.1.1.retained eta.1.1.tail.1
      (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound)
      (Classical.decPred _) D
      (singletonPairSelected eta b cap) (Classical.decPred _)
      (data.upper cap) (singletonPairWindowScreen eta b cap)
      (Classical.decPred _)
      (positiveInterfaceExternalPairSourcePredicate_forward_singleton eta b
        cap threshold bound)
      (tilingAwayPointMass_normalization_ne_zero_of_upper_pos
        t eta.1.1.start eta.1.1.retained D (data.upper cap)
          (data.upper_pos cap))
  unfold singletonPairWindowScreenMass
  unfold externalAcceptedThetaCarrier
  convert h using 1
  · simp only [D, data, singletonPairFiber, singletonFiber,
      pairCoarseIndex, singletonSupportedIndex, withSelected,
      TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber,
      tilingDistinguishedAssignmentMass]
    unfold singletonPairWindowScreen
    unfold screenMass
    apply congrArg₂ (· * ·)
    · apply Finset.sum_congr rfl
      intro ell _hell
      by_cases hs : (ell (singletonPairCoordinate eta b) : ℕ) ∈
          positiveInterfacePairWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell
      · simp only [hs, if_true]
        congr 1
      · simp only [hs, if_false]
    · rfl

/-- After the sharp singleton tail estimate, the exact pair source mass is
paid by the finite collection of honest singleton actual-rank fibres. -/
theorem positiveInterfaceExternalPairSourceStoppedGeometricMass_le_exp_mul_singletonSum
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hthick : m / 2 ≤ Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
    (him : Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) ≤ m)
    (hfit : (shell + 2) * shellWidth48 m ≤ m)
    (hwidthDeviation :
      24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hbad : ¬ SmallWindow.windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (HLOZPositiveInterfacePhysicalWindowRatio.acceptedPhysicalDeficitFailureWindow
            m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            (shell + 1)) ≤
        positiveInterfaceRatioConstant * SmallWindow.windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (HLOZPositiveInterfacePhysicalWindowRatio.acceptedPhysicalDeficitFailureWindow
            m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            shell)) :
    let pairData := PositiveInterfaceExternalPairFiber eta
    let data := singletonPairFiber eta b
    prefixedTilingStoppedAcceptedGeometricMass
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (pairData.coordinateCap cap) eta.1.1.tail.1
        (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound) ≤
      (2 * Real.exp (-17 * balanceRateScale m)) *
        ∑ delta : SourceActualDeltaIndex data,
          prefixedTilingStoppedAcceptedGeometricMass
            (sourceActualDeltaStoppingTime data cap delta)
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (data.coordinateCap cap) eta.1.1.tail.1
            (actualDeltaSelectedPredicate data
              (singletonPairSelected eta b) cap delta) := by
  classical
  dsimp only
  let pairData := PositiveInterfaceExternalPairFiber eta
  let data := singletonPairFiber eta b
  let carrier := externalAcceptedThetaCarrier
    (withSelected data (singletonPairSelected eta b)) cap
  let sourceMass := prefixedTilingStoppedAcceptedGeometricMass
    (truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (pairData.coordinateCap cap) eta.1.1.tail.1
    (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound)
  let rankMass := fun delta : SourceActualDeltaIndex data ↦
    prefixedTilingStoppedAcceptedGeometricMass
      (sourceActualDeltaStoppingTime data cap delta)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (data.coordinateCap cap) eta.1.1.tail.1
      (actualDeltaSelectedPredicate data
        (singletonPairSelected eta b) cap delta)
  have hsource :=
    positiveInterfaceExternalPairSourceStoppedGeometricMass_le_singleton
      eta b cap threshold bound
  have hranks := sum_actualDeltaSelectedStoppedGeometricMass_eq_carrier data
    (singletonPairSelected eta b) cap
    (singletonPair_actualDeltaAccepted eta b hm hk hfixedPos cap)
  have hscreen := singletonPairWindowScreenMass_le_of_not_windowRatio
    eta cap b harithmetic hwidthFour hthick him hfit hwidthDeviation
      hdeviationLevel hbad
  have hcarrier : 0 ≤ carrier := externalAcceptedThetaCarrier_nonneg
    (withSelected data (singletonPairSelected eta b)) cap
  change sourceMass ≤ _ at hsource
  change (∑ delta, rankMass delta) = carrier at hranks
  calc
    sourceMass ≤ singletonPairWindowScreenMass eta b cap * carrier := hsource
    _ ≤ (2 * Real.exp (-17 * balanceRateScale m)) * carrier :=
      mul_le_mul_of_nonneg_right hscreen hcarrier
    _ = (2 * Real.exp (-17 * balanceRateScale m)) *
        ∑ delta, rankMass delta := by rw [hranks]

end

end Erdos1165.HLOZPositiveInterfacePairWindowTailSingleton
