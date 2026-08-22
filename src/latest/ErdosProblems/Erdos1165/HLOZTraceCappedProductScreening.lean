import ErdosProblems.Erdos1165.HLOZTraceScreenPackage

/-!
# Tiling-independent capped product trace screens

`UpperProductScreenData` is specialized to the two fixed-letter horizontal
deletion orientations.  HLOZ uses six domino tilings, including the two
state-dependent column tilings.  This module keeps the same sound trace
partition interface but uses the already checked, coordinate-system-neutral
`CappedProductScreenCertificate` as its quantitative field.

The certificate still contains the literal finite product probability, its
finite numerical bound, and the exact restricted-real disintegration.  Thus
this generalization does not replace the product law by a path-level
transition estimate.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZTraceCappedProductScreening

open HLOZPathEvents HLOZSpatialAdapter PreStoppingConditionalLaw
open HLOZStoppedProductRefinement HLOZStoppedSpatialScreening

noncomputable section

/-- A sound countable trace partition equipped with literal capped product
certificates.  The coordinate system used to prove each product probability
is deliberately abstract. -/
structure TraceCappedProductScreening {Index : Type*} [Countable Index]
    (stage next : Set WalkPath) (cost : ℝ≥0∞) where
  piece : Index → Set WalkPath
  measurable_piece : ∀ z, MeasurableSet (piece z)
  disjoint_piece : Pairwise fun z w ↦ Disjoint (piece z) (piece w)
  union_piece : (⋃ z, piece z) = stage
  next_subset_stage : next ⊆ stage
  certificate : CappedProductScreenCertificate piece next cost

theorem transition_measure_le_of_traceCappedProductScreening
    {Index : Type*} [Countable Index]
    (stage next : Set WalkPath) (hnext : MeasurableSet next)
    (cost : ℝ≥0∞) (hcost : cost ≠ ∞)
    (screening : TraceCappedProductScreening (Index := Index)
      stage next cost) :
    simpleRandomWalk next ≤ cost * simpleRandomWalk stage := by
  have hscreen : AtomwiseRestrictedRealScreen screening.piece next cost :=
    atomwiseRestrictedRealScreen_of_cappedProductCertificate
      screening.piece next cost hcost screening.certificate
  exact measure_next_le_of_atomwiseTransition screening.piece
    screening.measurable_piece screening.disjoint_piece screening.union_piece
    screening.next_subset_stage
    (pathTransitionDomination_of_atomwiseRestrictedRealScreen
      screening.piece hnext hcost hscreen)

/-- Existentially hide the countable tiling-trace code. -/
structure SomeTraceCappedProductScreening
    (stage next : Set WalkPath) (cost : ℝ≥0∞) where
  Index : Type
  countableIndex : Countable Index
  screening : @TraceCappedProductScreening Index countableIndex stage next cost

/-- The three six-tiling-compatible product screens at one level and mesh
branch. -/
structure ThreeTransitionCappedTraceScreens
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) where
  first : SomeTraceCappedProductScreening (firstCreationStage m)
    (firstTransitionEvent t m a) (UpperCanonical.hlozTransitionCost K m)
  second : SomeTraceCappedProductScreening (firstTransitionEvent t m a)
    (secondTransitionEvent t m a) (UpperCanonical.hlozTransitionCost K m)
  third : SomeTraceCappedProductScreening (secondTransitionEvent t m a)
    (screenedThirdTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)

structure AllLevelCappedTraceScreenPackage (K : ℝ≥0) where
  screens : ∀ t m a, ThreeTransitionCappedTraceScreens K t m a

theorem firstTransition_measure_le_of_cappedPackage (K : ℝ≥0)
    (package : AllLevelCappedTraceScreenPackage K)
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    simpleRandomWalk (firstTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m := by
  let cert := (package.screens t m a).first
  have hstage : simpleRandomWalk (firstCreationStage m) ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ (firstCreationStage m))
  calc
    simpleRandomWalk (firstTransitionEvent t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk (firstCreationStage m) :=
      @transition_measure_le_of_traceCappedProductScreening cert.Index
        cert.countableIndex (firstCreationStage m)
        (firstTransitionEvent t m a) (measurableSet_firstTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m)
        (hlozTransitionCost_ne_top K m) cert.screening
    _ ≤ UpperCanonical.hlozTransitionCost K m * 1 := by
      simpa only [mul_comm] using
        (mul_le_mul_left hstage (UpperCanonical.hlozTransitionCost K m))
    _ = UpperCanonical.hlozTransitionCost K m := mul_one _

theorem secondTransition_measure_le_of_cappedPackage (K : ℝ≥0)
    (package : AllLevelCappedTraceScreenPackage K)
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    simpleRandomWalk (secondTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (firstTransitionEvent t m a) := by
  let cert := (package.screens t m a).second
  exact @transition_measure_le_of_traceCappedProductScreening cert.Index
    cert.countableIndex (firstTransitionEvent t m a)
    (secondTransitionEvent t m a) (measurableSet_secondTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (hlozTransitionCost_ne_top K m) cert.screening

theorem screenedThirdTransition_measure_le_of_cappedPackage (K : ℝ≥0)
    (package : AllLevelCappedTraceScreenPackage K)
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (secondTransitionEvent t m a) := by
  let cert := (package.screens t m a).third
  exact @transition_measure_le_of_traceCappedProductScreening cert.Index
    cert.countableIndex (secondTransitionEvent t m a)
    (screenedThirdTransitionEvent t m a)
    (measurableSet_screenedThirdTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (hlozTransitionCost_ne_top K m) cert.screening

/-- Direct upper endgame from all-six capped product certificates. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_cappedPackage
    (K : ℝ≥0) (package : AllLevelCappedTraceScreenPackage K)
    (hexception : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in Filter.atTop,
      favoriteCount s n ≤ 3 := by
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_path_transition_estimates
      K
  · intro t m a _
    exact firstTransition_measure_le_of_cappedPackage K package t m a
  · intro t m a _
    exact secondTransition_measure_le_of_cappedPackage K package t m a
  · intro t m a _
    exact screenedThirdTransition_measure_le_of_cappedPackage K package t m a
  · exact hexception

end

end Erdos1165.HLOZTraceCappedProductScreening
