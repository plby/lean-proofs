import ErdosProblems.Erdos1165.HLOZTracePartitionAdapter

/-!
# Exact product disintegration from variable stopped-prefix masses

This module is the measure-theoretic seam between a variable, prefix-free
stopped insertion fibre and `UpperProductScreenData`.  It does not condition
on the physical stopping time.  Instead, one proves an equality of two
explicit finite geometric coordinate sums.  The common external-word factor
is then transported to the corresponding restricted path measures.

For the six HLOZ tilings, the remaining combinatorial input is to identify
the stopped/favorite predicate with a predicate on distinguished domino
coordinates together with the corrected coordinatewise away cutoff.  That
input belongs to the tiling-specific coordinate decomposition; it is not a
path-measure inequality.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.VariableStoppedProductDisintegration

open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber
open PreStoppingFiber PreStoppingConditionalLaw PrefixConditionalLaw
open VariableStoppedTracePartition HLOZStoppedSpatialScreening
open HLOZStoppedProductRefinement HLOZTraceScreenPackage
open HLOZTracePartitionAdapter HLOZPathEvents

noncomputable section

/-- The explicit finite geometric mass of the stopped-accepted coordinates
selected by `P`.  The stopping acceptance is part of the finite index, so
this definition does not hide a physical-time conditioning. -/
noncomputable def stoppedAcceptedGeometricMass
    (tau : StepPath → ℕ) {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (cap : ℕ) (tail : List Direction)
    (P : CappedCoordinates i cap → Prop) : ℝ :=
  ∑ q : AcceptedCappedCoordinates tau r cap tail P,
    gapVectorMass (fun j ↦ (q.1 j : ℕ))

theorem gapVectorMass_nonneg {i : ℕ} (q : Fin (i + 1) → ℕ) :
    0 ≤ gapVectorMass q := by
  unfold gapVectorMass
  exact Finset.prod_nonneg fun j _ ↦ geometricGapMass_nonneg (q j)

theorem stoppedAcceptedGeometricMass_nonneg
    (tau : StepPath → ℕ) {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (cap : ℕ) (tail : List Direction)
    (P : CappedCoordinates i cap → Prop) :
    0 ≤ stoppedAcceptedGeometricMass tau r cap tail P := by
  unfold stoppedAcceptedGeometricMass
  exact Finset.sum_nonneg fun q _ ↦ gapVectorMass_nonneg _

/-! ## Cancellation of an arbitrary distinguished-coordinate marginal -/

/-- Unnormalized mass after arbitrary finite distinguished data have been
attached to one away-domino total vector. -/
noncomputable def distinguishedAwayMass
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ)
    {delta : Type*} [Fintype delta] (distinguishedMass : delta → ℝ)
    (ell : UpperTruncatedDominoTotals x r D upper) : ℝ :=
  ∑ d, upperTotalsJointMass x r D upper ell * distinguishedMass d

/-- Summing an arbitrary common distinguished-coordinate factor does not
alter an away-total screen.  This is the finite algebra needed after a
tiling-specific decoder has proved that all stopping/favorite conditions are
carried by the distinguished coordinates. -/
theorem upperProductScreenMass_mul_distinguishedBase
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ)
    (screen : UpperTruncatedDominoTotals x r D upper → Prop)
    [DecidablePred screen]
    {delta : Type*} [Fintype delta] (distinguishedMass : delta → ℝ)
    (htotal : (∑ ell : UpperTruncatedDominoTotals x r D upper,
      upperTotalsJointMass x r D upper ell) ≠ 0) :
    upperProductScreenMass x r D upper screen *
        (∑ ell : UpperTruncatedDominoTotals x r D upper,
          distinguishedAwayMass x r D upper distinguishedMass ell) =
      ∑ ell : UpperTruncatedDominoTotals x r D upper,
        if screen ell then
          distinguishedAwayMass x r D upper distinguishedMass ell else 0 := by
  classical
  let total := ∑ ell : UpperTruncatedDominoTotals x r D upper,
    upperTotalsJointMass x r D upper ell
  let selected := ∑ ell : UpperTruncatedDominoTotals x r D upper,
    if screen ell then upperTotalsJointMass x r D upper ell else 0
  let dist := ∑ d, distinguishedMass d
  have hproduct : upperProductScreenMass x r D upper screen =
      selected / total := by
    unfold upperProductScreenMass normalizedUpperTotalsMass selected total
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ell _
    by_cases hell : screen ell <;> simp [hell]
  have hbase :
      (∑ ell : UpperTruncatedDominoTotals x r D upper,
        distinguishedAwayMass x r D upper distinguishedMass ell) =
        total * dist := by
    unfold distinguishedAwayMass total dist
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_mul]
  have hscreen :
      (∑ ell : UpperTruncatedDominoTotals x r D upper,
        if screen ell then
          distinguishedAwayMass x r D upper distinguishedMass ell else 0) =
        selected * dist := by
    unfold distinguishedAwayMass selected dist
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ell _
    by_cases hell : screen ell <;> simp [hell, Finset.mul_sum]
  rw [hproduct, hbase, hscreen]
  field_simp [total, htotal]

/-- Ready-to-use coordinate identity.  A tiling decoder need only show that
its accepted base and screened sums are respectively the full and selected
distinguished-away marginal sums. -/
theorem stoppedAcceptedGeometricMass_eq_upperProduct_mul_of_marginals
    {tau : StepPath → ℕ} {o : Orientation} {i cap : ℕ}
    (r : Fin i → RetainedBlock o) (tail : List Direction)
    (base screened : CappedCoordinates i cap → Prop)
    (x : Point) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ)
    (screen : UpperTruncatedDominoTotals x r D upper → Prop)
    [DecidablePred screen]
    {delta : Type*} [Fintype delta] (distinguishedMass : delta → ℝ)
    (htotal : (∑ ell : UpperTruncatedDominoTotals x r D upper,
      upperTotalsJointMass x r D upper ell) ≠ 0)
    (hbase : stoppedAcceptedGeometricMass tau r cap tail base =
      ∑ ell : UpperTruncatedDominoTotals x r D upper,
        distinguishedAwayMass x r D upper distinguishedMass ell)
    (hscreen : stoppedAcceptedGeometricMass tau r cap tail screened =
      ∑ ell : UpperTruncatedDominoTotals x r D upper,
        if screen ell then
          distinguishedAwayMass x r D upper distinguishedMass ell else 0) :
    stoppedAcceptedGeometricMass tau r cap tail screened =
      upperProductScreenMass x r D upper screen *
        stoppedAcceptedGeometricMass tau r cap tail base := by
  rw [hscreen, hbase]
  exact (upperProductScreenMass_mul_distinguishedBase x r D upper screen
    distinguishedMass htotal).symm

theorem prefixFiberConstant_nonneg (i : ℕ) (tail : List Direction) :
    0 ≤ prefixFiberConstant i tail := by
  unfold prefixFiberConstant
  positivity

/-- The exact real mass version of finite stopped-prefix mass transport. -/
theorem fairSteps_real_preStoppingFiberEvent
    {tau : StepPath → ℕ} (htau : IsFiniteStoppingTime tau)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (cap : ℕ) (tail : List Direction)
    (P : CappedCoordinates i cap → Prop) :
    fairSteps.real (preStoppingFiberEvent tau r cap tail P) =
      prefixFiberConstant i tail *
        stoppedAcceptedGeometricMass tau r cap tail P := by
  rw [Measure.real, fairSteps_preStoppingFiberEvent_eq_geometricSum
    htau r cap tail P]
  exact ENNReal.toReal_ofReal (mul_nonneg
    (prefixFiberConstant_nonneg i tail)
    (stoppedAcceptedGeometricMass_nonneg tau r cap tail P))

/-- Monotonicity of the stopped-prefix event in its coordinate predicate. -/
theorem preStoppingFiberEvent_mono
    (tau : StepPath → ℕ) {o : Orientation} {i cap : ℕ}
    (r : Fin i → RetainedBlock o) (tail : List Direction)
    {P Q : CappedCoordinates i cap → Prop}
    (hQP : ∀ q, Q q → P q) :
    preStoppingFiberEvent tau r cap tail Q ⊆
      preStoppingFiberEvent tau r cap tail P := by
  classical
  intro omega homega
  rcases Set.mem_iUnion.mp homega with ⟨q, hq⟩
  apply Set.mem_iUnion.mpr
  exact ⟨⟨q.1, hQP q.1 q.2.1, q.2.2⟩, hq⟩

/-- Restricting to any ambient fine trace piece does not change the real
mass of a lifted measurable stopped subfibre already contained in it. -/
theorem restrictedReal_walkLift_of_subset
    {piece : Set WalkPath} {A : Set StepPath} (hA : MeasurableSet A)
    (hsub : walkLift A ⊆ piece) :
    (simpleRandomWalk.restrict piece).real (walkLift A) = fairSteps.real A := by
  have hLA : MeasurableSet (walkLift A) := measurableSet_walkLift hA
  change (simpleRandomWalk.restrict piece (walkLift A)).toReal =
    (fairSteps A).toReal
  rw [Measure.restrict_apply hLA, inter_eq_left.mpr hsub,
    simpleRandomWalk_walkLift hA]

/-- The literal capped restricted-real product identity.  Its hypothesis is
an equality of finite geometric coordinate sums, not a path-space measure
identity and not the desired transition estimate. -/
theorem stoppedCapped_restrictedReal_productIdentity
    {piece : Set WalkPath} {tau : StepPath → ℕ}
    (htau : IsFiniteStoppingTime tau)
    {o : Orientation} {i cap : ℕ} (r : Fin i → RetainedBlock o)
    (tail : List Direction)
    (base screened : CappedCoordinates i cap → Prop)
    (hsub : ∀ q, screened q → base q)
    (hpiece : walkLift (preStoppingFiberEvent tau r cap tail base) ⊆ piece)
    (productProbability : ℝ)
    (hmass : stoppedAcceptedGeometricMass tau r cap tail screened =
      productProbability *
        stoppedAcceptedGeometricMass tau r cap tail base) :
    (simpleRandomWalk.restrict piece).real
        (walkLift (preStoppingFiberEvent tau r cap tail screened)) =
      productProbability *
        (simpleRandomWalk.restrict piece).real
          (walkLift (preStoppingFiberEvent tau r cap tail base)) := by
  have hbaseMeas : MeasurableSet
      (preStoppingFiberEvent tau r cap tail base) :=
    measurableSet_preStoppingFiberEvent htau r cap tail base
  have hscreenMeas : MeasurableSet
      (preStoppingFiberEvent tau r cap tail screened) :=
    measurableSet_preStoppingFiberEvent htau r cap tail screened
  have hscreenPiece :
      walkLift (preStoppingFiberEvent tau r cap tail screened) ⊆ piece :=
    by
      intro s hs
      apply hpiece
      exact ⟨hs.1, preStoppingFiberEvent_mono tau r tail hsub hs.2⟩
  rw [restrictedReal_walkLift_of_subset hscreenMeas hscreenPiece,
    restrictedReal_walkLift_of_subset hbaseMeas hpiece,
    fairSteps_real_preStoppingFiberEvent htau r cap tail screened,
    fairSteps_real_preStoppingFiberEvent htau r cap tail base, hmass]
  ring

/-! ## A constructor for `UpperProductScreenData` -/

/-- All pathwise data needed to turn a finite coordinate factorization into
literal `UpperProductScreenData`.  The decisive `coordinate_identity` field
is an equality of explicit finite sums.  In the intended application it is
proved by grouping insertion coordinates by tiling domino, marginalizing
the distinguished coordinates, and applying the corrected away cutoff
`m - fixedPrefixMax`.

`monotone_screened` and `transition_covered` are cap-exhaustion statements;
neither contains a probability estimate. -/
structure StoppedCoordinateProductSpec {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath) where
  orientation : index → ℕ → Orientation
  retainedCount : index → ℕ → ℕ
  start : index → ℕ → Point
  retained : ∀ z cap,
    Fin (retainedCount z cap) → RetainedBlock (orientation z cap)
  tail : index → ℕ → List Direction
  stoppingTime : index → ℕ → StepPath → ℕ
  isStoppingTime : ∀ z cap, IsFiniteStoppingTime (stoppingTime z cap)
  basePredicate : ∀ z cap,
    CappedCoordinates (retainedCount z cap) cap → Prop
  screenedPredicate : ∀ z cap,
    CappedCoordinates (retainedCount z cap) cap → Prop
  screened_subset_base : ∀ z cap q,
    screenedPredicate z cap q → basePredicate z cap q
  base_subset_piece : ∀ z cap,
    walkLift (preStoppingFiberEvent (stoppingTime z cap)
      (retained z cap) cap (tail z cap) (basePredicate z cap)) ⊆ piece z
  distinguished : index → ℕ → Finset Point
  upper : ∀ z cap,
    ExternalDomino (start z cap) (retained z cap) → ℕ
  accepts : ∀ z cap,
    UpperTruncatedDominoTotals (start z cap) (retained z cap)
      (distinguished z cap) (upper z cap) → Bool
  coordinate_identity : ∀ z cap,
    stoppedAcceptedGeometricMass (stoppingTime z cap) (retained z cap) cap
        (tail z cap) (screenedPredicate z cap) =
      upperProductScreenMass (start z cap) (retained z cap)
          (distinguished z cap) (upper z cap)
          (fun ell ↦ accepts z cap ell = true) *
        stoppedAcceptedGeometricMass (stoppingTime z cap) (retained z cap) cap
          (tail z cap) (basePredicate z cap)
  monotone_screened : ∀ z, Monotone fun cap ↦
    walkLift (preStoppingFiberEvent (stoppingTime z cap)
      (retained z cap) cap (tail z cap) (screenedPredicate z cap))
  transition_covered : ∀ z, piece z ∩ next ⊆ ⋃ cap,
    walkLift (preStoppingFiberEvent (stoppingTime z cap)
      (retained z cap) cap (tail z cap) (screenedPredicate z cap))

/-- Construct the literal capped product disintegration.  No measure-law
field remains: `disintegrate` is proved from `coordinate_identity` and the
prefix-free stopped-cylinder mass theorem. -/
def upperProductScreenDataOfStoppedCoordinateSpec
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    (spec : StoppedCoordinateProductSpec piece next) :
    UpperProductScreenData piece next where
  orientation := spec.orientation
  retainedCount := spec.retainedCount
  start := spec.start
  retained := spec.retained
  distinguished := spec.distinguished
  upper := spec.upper
  accepts := spec.accepts
  screened z cap := walkLift
    (preStoppingFiberEvent (spec.stoppingTime z cap) (spec.retained z cap)
      cap (spec.tail z cap) (spec.screenedPredicate z cap))
  fiber z cap := walkLift
    (preStoppingFiberEvent (spec.stoppingTime z cap) (spec.retained z cap)
      cap (spec.tail z cap) (spec.basePredicate z cap))
  measurable_screened z cap := measurableSet_walkLift
    (measurableSet_preStoppingFiberEvent (spec.isStoppingTime z cap)
      (spec.retained z cap) cap (spec.tail z cap)
      (spec.screenedPredicate z cap))
  monotone_screened := spec.monotone_screened
  transition_covered := spec.transition_covered
  disintegrate z cap :=
    stoppedCapped_restrictedReal_productIdentity
      (spec.isStoppingTime z cap) (spec.retained z cap) (spec.tail z cap)
      (spec.basePredicate z cap) (spec.screenedPredicate z cap)
      (spec.screened_subset_base z cap) (spec.base_subset_piece z cap)
      (upperProductScreenMass (spec.start z cap) (spec.retained z cap)
        (spec.distinguished z cap) (spec.upper z cap)
        (fun ell ↦ spec.accepts z cap ell = true))
      (spec.coordinate_identity z cap)

theorem finiteProductScreenBound_of_stoppedCoordinateSpec
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    (spec : StoppedCoordinateProductSpec piece next) (cost : ℝ≥0∞)
    (hbound : ∀ z cap,
      upperProductScreenMass (spec.start z cap) (spec.retained z cap)
          (spec.distinguished z cap) (spec.upper z cap)
          (fun ell ↦ spec.accepts z cap ell = true) ≤ cost.toReal) :
    FiniteProductScreenBound
      (upperProductScreenDataOfStoppedCoordinateSpec spec) cost :=
  hbound

/-! ## Direct consumers for the three sound trace partitions -/

/-- First-transition package from a literal stopped-coordinate spec.  The
only remaining quantitative input is the finite product tail bound. -/
def firstTraceScreenOfStoppedCoordinateSpec
    (o : Orientation) (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (spec : StoppedCoordinateProductSpec
      (favoriteStagePiece o m 1 (firstCreationStage m))
      (firstTransitionEvent t m a))
    (hbound : ∀ z cap,
      upperProductScreenMass (spec.start z cap) (spec.retained z cap)
          (spec.distinguished z cap) (spec.upper z cap)
          (fun ell ↦ spec.accepts z cap ell = true) ≤
        (UpperCanonical.hlozTransitionCost K m).toReal) :
    SomeTraceUpperProductScreening (firstCreationStage m)
      (firstTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m) :=
  firstTraceScreenOfProductData o K t m a
    (upperProductScreenDataOfStoppedCoordinateSpec spec)
    (finiteProductScreenBound_of_stoppedCoordinateSpec spec _ hbound)

/-- Second-transition package from the rank-two variable stopped fibre. -/
def secondTraceScreenOfStoppedCoordinateSpec
    (o : Orientation) (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (spec : StoppedCoordinateProductSpec
      (favoriteStagePiece o m 2 (firstTransitionEvent t m a))
      (secondTransitionEvent t m a))
    (hbound : ∀ z cap,
      upperProductScreenMass (spec.start z cap) (spec.retained z cap)
          (spec.distinguished z cap) (spec.upper z cap)
          (fun ell ↦ spec.accepts z cap ell = true) ≤
        (UpperCanonical.hlozTransitionCost K m).toReal) :
    SomeTraceUpperProductScreening (firstTransitionEvent t m a)
      (secondTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m) :=
  secondTraceScreenOfProductData o K t m a
    (upperProductScreenDataOfStoppedCoordinateSpec spec)
    (finiteProductScreenBound_of_stoppedCoordinateSpec spec _ hbound)

/-- Third-transition package from the rank-three variable stopped fibre. -/
def thirdTraceScreenOfStoppedCoordinateSpec
    (o : Orientation) (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (spec : StoppedCoordinateProductSpec
      (favoriteStagePiece o m 3 (secondTransitionEvent t m a))
      (screenedThirdTransitionEvent t m a))
    (hbound : ∀ z cap,
      upperProductScreenMass (spec.start z cap) (spec.retained z cap)
          (spec.distinguished z cap) (spec.upper z cap)
          (fun ell ↦ spec.accepts z cap ell = true) ≤
        (UpperCanonical.hlozTransitionCost K m).toReal) :
    SomeTraceUpperProductScreening (secondTransitionEvent t m a)
      (screenedThirdTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m) :=
  thirdTraceScreenOfProductData o K t m a
    (upperProductScreenDataOfStoppedCoordinateSpec spec)
    (finiteProductScreenBound_of_stoppedCoordinateSpec spec _ hbound)

end

end Erdos1165.VariableStoppedProductDisintegration
