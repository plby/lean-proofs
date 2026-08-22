/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingConditionalCappedMarginalization
import ErdosProblems.Erdos1165.TilingPrefixedStoppedProductDisintegration

/-!
# Conditional marginalization for physical-prefix stopped fibers

Endpoint-oriented stopped fibers may begin after a fixed physical prefix.
Their capped family may also use a trace-dependent cofinal schedule of actual
coordinate cutoffs.  This file proves the exact conditional finite-product
identity in that setting and converts it directly to `CoordinateMassSpec`.

The physical prefix occurs only in the common factor
`prefixedPrefixFiberConstant`; it cancels from the conditional product ratio.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingPrefixedConditionalCappedMarginalization

open CappedCoordinateMassCertificate FiniteDominoProductLaw
open PathInsertion PreStoppingFiber SpatialInsertionFiber
open TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A prefixed accepted coordinate mass factors into its away-screen mass
and the same distinguished-coordinate common term as in the origin-start
fiber. -/
theorem prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
    (tau : StepPath → ℕ) (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction)
    (predicate : TilingCappedCoordinates i cap → Prop)
    [DecidablePred predicate]
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (upper : TilingAwayDomino t x r D → ℕ)
    (screen : TruncatedTotals upper → Prop) [DecidablePred screen]
    (hfactor : ∀ q,
      predicate q ∧ PrefixedTilingStoppingAccepted tau initial t x r
          (fun k ↦ (q k : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper screen
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass (tilingAwayPointMass (cap := cap) t x r D) upper ell) ≠ 0) :
    prefixedTilingStoppedAcceptedGeometricMass
        tau initial t x r cap tail predicate =
      screenMass (tilingAwayPointMass (cap := cap) t x r D) upper screen *
        ∑ ell : TruncatedTotals upper,
          distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ell := by
  classical
  rw [prefixedTilingStoppedAcceptedGeometricMass_eq_indicatorSum]
  calc
    (∑ q : TilingCappedCoordinates i cap,
        if predicate q ∧ PrefixedTilingStoppingAccepted tau initial t x r
            (fun k ↦ (q k : ℕ)) tail then
          gapVectorMass (fun k ↦ (q k : ℕ)) else 0) =
        ∑ q : TilingCappedCoordinates i cap,
          if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
              TilingAwayTotalsScreen t x r D upper screen
                ((splitTilingCoordinatesEquiv t x r D q).2) then
            gapVectorMass (fun k ↦ (q k : ℕ)) else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      exact if_congr (hfactor q) rfl rfl
    _ = ∑ ell : TruncatedTotals upper,
        if screen ell then
          distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ell
        else 0 :=
      tilingCappedScreenedMass_factorization
        t x r D selected upper screen
    _ = screenMass (tilingAwayPointMass (cap := cap) t x r D) upper screen *
        ∑ ell : TruncatedTotals upper,
          distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ell :=
      (screenMass_mul_distinguishedBase
        (tilingAwayPointMass (cap := cap) t x r D) upper screen
        (fun d ↦ if selected d then
          tilingDistinguishedAssignmentMass t x r D d else 0) htotal).symm

/-- Exact conditional factorization for a prefixed stopped fiber. -/
theorem prefixedTilingStoppedAcceptedGeometricMass_conditional_product_of_factorization
    (tau : StepPath → ℕ) (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction)
    (basePredicate screenedPredicate :
      TilingCappedCoordinates i cap → Prop)
    [DecidablePred basePredicate] [DecidablePred screenedPredicate]
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (upper : TilingAwayDomino t x r D → ℕ)
    (baseAccepts screenedAccepts : TruncatedTotals upper → Prop)
    [DecidablePred baseAccepts] [DecidablePred screenedAccepts]
    (hbase : ∀ q,
      basePredicate q ∧ PrefixedTilingStoppingAccepted tau initial t x r
          (fun k ↦ (q k : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper baseAccepts
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (hscreened : ∀ q,
      screenedPredicate q ∧
          PrefixedTilingStoppingAccepted tau initial t x r
            (fun k ↦ (q k : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper screenedAccepts
            ((splitTilingCoordinatesEquiv t x r D q).2))
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass (tilingAwayPointMass (cap := cap) t x r D) upper ell) ≠ 0)
    (hbaseMass : screenMass
      (tilingAwayPointMass (cap := cap) t x r D) upper baseAccepts ≠ 0) :
    prefixedTilingStoppedAcceptedGeometricMass tau initial t x r cap tail
        screenedPredicate =
      conditionalScreenMass
          (tilingAwayPointMass (cap := cap) t x r D) upper
          baseAccepts screenedAccepts *
        prefixedTilingStoppedAcceptedGeometricMass tau initial t x r cap tail
          basePredicate := by
  let common := ∑ ell : TruncatedTotals upper,
    distinguishedAwayMass
      (tilingAwayPointMass (cap := cap) t x r D) upper
      (fun d ↦ if selected d then
        tilingDistinguishedAssignmentMass t x r D d else 0) ell
  rw [prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
      tau initial t x r tail screenedPredicate D selected upper
      screenedAccepts hscreened htotal,
    prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
      tau initial t x r tail basePredicate D selected upper baseAccepts
      hbase htotal]
  change screenMass
      (tilingAwayPointMass (cap := cap) t x r D) upper screenedAccepts * common =
    conditionalScreenMass
        (tilingAwayPointMass (cap := cap) t x r D) upper
        baseAccepts screenedAccepts *
      (screenMass (tilingAwayPointMass (cap := cap) t x r D) upper
        baseAccepts * common)
  rw [← mul_assoc, conditionalScreenMass_mul_base _ _ _ _ hbaseMass]

/-! ## Scheduled prefixed conditional data -/

/-- Conditional factored data with a physical initial prefix and an arbitrary
actual coordinate cutoff at each logical cap-union stage. -/
structure TilingPrefixedConditionalFactoredStoppedCoordinateData
    {index : Type*} (piece : index → Set WalkPath) (next : Set WalkPath)
    (cost : ℝ≥0∞) where
  tiling : index → ℕ → DominoTiling
  retainedCount : index → ℕ → ℕ
  coordinateCap : index → ℕ → ℕ
  initial : index → ℕ → List Direction
  start : index → ℕ → Point
  retained : ∀ z cap,
    TilingRetainedWord (tiling z cap) (start z cap) (retainedCount z cap)
  tail : index → ℕ → List Direction
  stoppingTime : index → ℕ → StepPath → ℕ
  isStoppingTime : ∀ z cap, IsFiniteStoppingTime (stoppingTime z cap)
  basePredicate : ∀ z cap,
    TilingCappedCoordinates (retainedCount z cap) (coordinateCap z cap) → Prop
  screenedPredicate : ∀ z cap,
    TilingCappedCoordinates (retainedCount z cap) (coordinateCap z cap) → Prop
  screened_subset_base : ∀ z cap q,
    screenedPredicate z cap q → basePredicate z cap q
  base_subset_piece : ∀ z cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (stoppingTime z cap)
      (initial z cap) (tiling z cap) (start z cap) (retained z cap)
      (coordinateCap z cap) (tail z cap) (basePredicate z cap)) ⊆ piece z
  distinguished : index → ℕ → Finset Point
  selected : ∀ z cap,
    TilingDistinguishedCoordinates (cap := coordinateCap z cap)
      (tiling z cap) (start z cap) (retained z cap)
      (distinguished z cap) → Prop
  upper : ∀ z cap, TilingAwayDomino
    (tiling z cap) (start z cap) (retained z cap)
      (distinguished z cap) → ℕ
  baseAccepts : ∀ z cap, TruncatedTotals (upper z cap) → Bool
  screenedAccepts : ∀ z cap, TruncatedTotals (upper z cap) → Bool
  screenedAccepts_subset_base : ∀ z cap ell,
    screenedAccepts z cap ell = true → baseAccepts z cap ell = true
  base_factorization : ∀ z cap q,
    basePredicate z cap q ∧
        PrefixedTilingStoppingAccepted (stoppingTime z cap) (initial z cap)
          (tiling z cap) (start z cap) (retained z cap)
          (fun j ↦ (q j : ℕ)) (tail z cap) ↔
      selected z cap
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).1) ∧
        TilingAwayTotalsScreen (tiling z cap) (start z cap)
          (retained z cap) (distinguished z cap) (upper z cap)
          (fun ell ↦ baseAccepts z cap ell = true)
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).2)
  screened_factorization : ∀ z cap q,
    screenedPredicate z cap q ∧
        PrefixedTilingStoppingAccepted (stoppingTime z cap) (initial z cap)
          (tiling z cap) (start z cap) (retained z cap)
          (fun j ↦ (q j : ℕ)) (tail z cap) ↔
      selected z cap
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).1) ∧
        TilingAwayTotalsScreen (tiling z cap) (start z cap)
          (retained z cap) (distinguished z cap) (upper z cap)
          (fun ell ↦ screenedAccepts z cap ell = true)
          ((splitTilingCoordinatesEquiv (tiling z cap) (start z cap)
            (retained z cap) (distinguished z cap) q).2)
  upper_pos : ∀ z cap b, 0 < upper z cap b
  base_mass_ne_zero : ∀ z cap,
    screenMass
      (tilingAwayPointMass (cap := coordinateCap z cap)
        (tiling z cap) (start z cap) (retained z cap)
        (distinguished z cap)) (upper z cap)
      (fun ell ↦ baseAccepts z cap ell = true) ≠ 0
  monotone_screened : ∀ z, Monotone fun cap ↦
    walkLift (prefixedTilingPreStoppingFiberEvent (stoppingTime z cap)
      (initial z cap) (tiling z cap) (start z cap) (retained z cap)
      (coordinateCap z cap) (tail z cap) (screenedPredicate z cap))
  transition_covered : ∀ z, piece z ∩ next ⊆ ⋃ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (stoppingTime z cap)
      (initial z cap) (tiling z cap) (start z cap) (retained z cap)
      (coordinateCap z cap) (tail z cap) (screenedPredicate z cap))
  product_bound : ∀ z cap,
    conditionalScreenMass
      (tilingAwayPointMass (cap := coordinateCap z cap)
        (tiling z cap) (start z cap) (retained z cap)
        (distinguished z cap)) (upper z cap)
      (fun ell ↦ baseAccepts z cap ell = true)
      (fun ell ↦ screenedAccepts z cap ell = true) ≤ cost.toReal

/-- Exact coordinate-mass specification for scheduled physical-prefix
conditional data. -/
noncomputable def coordinateMassSpecOfTilingPrefixedConditionalFactoredData
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (data : TilingPrefixedConditionalFactoredStoppedCoordinateData
      piece next cost) : CoordinateMassSpec piece next cost := by
  classical
  refine {
    screened := fun z cap ↦ walkLift
      (prefixedTilingPreStoppingFiberEvent (data.stoppingTime z cap)
        (data.initial z cap) (data.tiling z cap) (data.start z cap)
        (data.retained z cap) (data.coordinateCap z cap) (data.tail z cap)
        (data.screenedPredicate z cap))
    fiber := fun z cap ↦ walkLift
      (prefixedTilingPreStoppingFiberEvent (data.stoppingTime z cap)
        (data.initial z cap) (data.tiling z cap) (data.start z cap)
        (data.retained z cap) (data.coordinateCap z cap) (data.tail z cap)
        (data.basePredicate z cap))
    measurable_screened := fun z cap ↦ measurableSet_walkLift
      (measurableSet_prefixedTilingPreStoppingFiberEvent
        (data.isStoppingTime z cap) (data.initial z cap)
        (data.tiling z cap) (data.start z cap) (data.retained z cap)
        (data.coordinateCap z cap) (data.tail z cap)
        (data.screenedPredicate z cap))
    measurable_fiber := fun z cap ↦ measurableSet_walkLift
      (measurableSet_prefixedTilingPreStoppingFiberEvent
        (data.isStoppingTime z cap) (data.initial z cap)
        (data.tiling z cap) (data.start z cap) (data.retained z cap)
        (data.coordinateCap z cap) (data.tail z cap)
        (data.basePredicate z cap))
    screened_subset_piece := ?_
    fiber_subset_piece := data.base_subset_piece
    monotone_screened := data.monotone_screened
    transition_covered := data.transition_covered
    commonFactor := fun z cap ↦ prefixedPrefixFiberConstant
      (data.initial z cap) (data.retainedCount z cap) (data.tail z cap)
    screenedCoordinateMass := fun z cap ↦
      prefixedTilingStoppedAcceptedGeometricMass
        (data.stoppingTime z cap) (data.initial z cap) (data.tiling z cap)
        (data.start z cap) (data.retained z cap) (data.coordinateCap z cap)
        (data.tail z cap) (data.screenedPredicate z cap)
    fiberCoordinateMass := fun z cap ↦
      prefixedTilingStoppedAcceptedGeometricMass
        (data.stoppingTime z cap) (data.initial z cap) (data.tiling z cap)
        (data.start z cap) (data.retained z cap) (data.coordinateCap z cap)
        (data.tail z cap) (data.basePredicate z cap)
    productProbability := fun z cap ↦ conditionalScreenMass
      (tilingAwayPointMass (cap := data.coordinateCap z cap)
        (data.tiling z cap) (data.start z cap) (data.retained z cap)
        (data.distinguished z cap)) (data.upper z cap)
      (fun ell ↦ data.baseAccepts z cap ell = true)
      (fun ell ↦ data.screenedAccepts z cap ell = true)
    coordinate_identity := ?_
    screened_event_mass := ?_
    fiber_event_mass := ?_
    product_bound := data.product_bound }
  · intro z cap s hs
    apply data.base_subset_piece z cap
    exact ⟨hs.1, prefixedTilingPreStoppingFiberEvent_mono
      (data.stoppingTime z cap) (data.initial z cap) (data.tiling z cap)
      (data.start z cap) (data.retained z cap) (data.tail z cap)
      (data.screened_subset_base z cap) hs.2⟩
  · intro z cap
    apply prefixedTilingStoppedAcceptedGeometricMass_conditional_product_of_factorization
      (data.stoppingTime z cap) (data.initial z cap) (data.tiling z cap)
      (data.start z cap) (data.retained z cap) (data.tail z cap)
      (data.basePredicate z cap) (data.screenedPredicate z cap)
      (data.distinguished z cap) (data.selected z cap) (data.upper z cap)
      (fun ell ↦ data.baseAccepts z cap ell = true)
      (fun ell ↦ data.screenedAccepts z cap ell = true)
      (data.base_factorization z cap) (data.screened_factorization z cap)
    · exact tilingAwayPointMass_normalization_ne_zero_of_upper_pos
        (data.tiling z cap) (data.start z cap) (data.retained z cap)
        (data.distinguished z cap) (data.upper z cap) (data.upper_pos z cap)
    · exact data.base_mass_ne_zero z cap
  · intro z cap
    exact simpleRandomWalk_real_walkLift_prefixedTilingPreStoppingFiberEvent
      (data.isStoppingTime z cap) (data.initial z cap) (data.tiling z cap)
      (data.start z cap) (data.retained z cap) (data.coordinateCap z cap)
      (data.tail z cap) (data.screenedPredicate z cap)
  · intro z cap
    exact simpleRandomWalk_real_walkLift_prefixedTilingPreStoppingFiberEvent
      (data.isStoppingTime z cap) (data.initial z cap) (data.tiling z cap)
      (data.start z cap) (data.retained z cap) (data.coordinateCap z cap)
      (data.tail z cap) (data.basePredicate z cap)

end

end Erdos1165.TilingPrefixedConditionalCappedMarginalization
