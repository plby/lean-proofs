/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingStoppedProductDisintegration
import ErdosProblems.Erdos1165.HLOZTracePartitionAdapter

/-!
# Three transition-stage adapters for all six tilings

These constructors close the deterministic countable-partition fields for
the first, second, and third HLOZ transition stages.  Their only remaining
inputs are literal state-dependent stopped-coordinate specifications.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.TilingTraceCappedStageAdapter

open HLOZPathEvents HLOZTracePartitionAdapter
open HLOZStoppedProductRefinement
open HLOZTraceCappedProductScreening TilingStoppedProductDisintegration
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def firstTilingTraceCappedScreenOfStoppedCoordinateSpec
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (spec : TilingStoppedCoordinateProductSpec
      (favoriteTilingStagePiece t m 1 (firstCreationStage m))
      (firstTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m)) :
    SomeTraceCappedProductScreening (firstCreationStage m)
      (firstTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m) := by
  have hstageMeasurable : MeasurableSet (firstCreationStage m) := by
    rw [← thresholdReachStage_one_eq_firstCreationStage]
    exact measurableSet_thresholdReachStage m 1
  have hstage : firstCreationStage m ⊆ thresholdReachStage m 1 := by
    rw [thresholdReachStage_one_eq_firstCreationStage]
  have hnext : firstTransitionEvent t m a ⊆ firstCreationStage m := by
    rw [← thresholdReachStage_one_eq_firstCreationStage]
    exact firstTransitionEvent_subset_thresholdReachStage_one t m a
  exact someFavoriteTilingTraceCappedScreenOfStoppedCoordinateSpec
    t m 1 (firstCreationStage m) (firstTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m) hstageMeasurable hstage hnext spec

def secondTilingTraceCappedScreenOfStoppedCoordinateSpec
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (spec : TilingStoppedCoordinateProductSpec
      (favoriteTilingStagePiece t m 2 (firstTransitionEvent t m a))
      (secondTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m)) :
    SomeTraceCappedProductScreening (firstTransitionEvent t m a)
      (secondTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m) :=
  someFavoriteTilingTraceCappedScreenOfStoppedCoordinateSpec
    t m 2 (firstTransitionEvent t m a) (secondTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (measurableSet_firstTransitionEvent t m a)
    (firstTransitionEvent_subset_thresholdReachStage_two t m a)
    (secondTransitionEvent_subset_first t m a) spec

def thirdTilingTraceCappedScreenOfStoppedCoordinateSpec
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (spec : TilingStoppedCoordinateProductSpec
      (favoriteTilingStagePiece t m 3 (secondTransitionEvent t m a))
      (screenedThirdTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m)) :
    SomeTraceCappedProductScreening (secondTransitionEvent t m a)
      (screenedThirdTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m) := by
  have hnext : screenedThirdTransitionEvent t m a ⊆
      secondTransitionEvent t m a := fun _ hs ↦
    thirdTransitionEvent_subset_second t m a hs.1
  exact someFavoriteTilingTraceCappedScreenOfStoppedCoordinateSpec
    t m 3 (secondTransitionEvent t m a) (screenedThirdTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (measurableSet_secondTransitionEvent t m a)
    (secondTransitionEvent_subset_thresholdReachStage_three t m a)
    hnext spec

/-- Assemble all three literal state-dependent stopped-coordinate families
into the all-level capped trace package consumed by the upper endgame. -/
def allLevelCappedTraceScreenPackageOfTilingStoppedCoordinateSpecs
    (K : ℝ≥0)
    (firstSpec : ∀ t m a,
      TilingStoppedCoordinateProductSpec
        (favoriteTilingStagePiece t m 1 (firstCreationStage m))
        (firstTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (secondSpec : ∀ t m a,
      TilingStoppedCoordinateProductSpec
        (favoriteTilingStagePiece t m 2 (firstTransitionEvent t m a))
        (secondTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (thirdSpec : ∀ t m a,
      TilingStoppedCoordinateProductSpec
        (favoriteTilingStagePiece t m 3 (secondTransitionEvent t m a))
        (screenedThirdTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    AllLevelCappedTraceScreenPackage K where
  screens t m a := {
    first := firstTilingTraceCappedScreenOfStoppedCoordinateSpec
      K t m a (firstSpec t m a)
    second := secondTilingTraceCappedScreenOfStoppedCoordinateSpec
      K t m a (secondSpec t m a)
    third := thirdTilingTraceCappedScreenOfStoppedCoordinateSpec
      K t m a (thirdSpec t m a) }

/-! ## Eventual specifications and the finite initial levels -/

set_option linter.constructorNameAsVariable false in
/-- The actual analytic product laws normally begin only after a fixed level.
For the finitely many earlier levels it suffices that the chosen transition
envelope is at least one. -/
theorem ae_eventually_favoriteCount_le_three_of_eventualTilingStoppedSpecs
    (K : ℝ≥0) (lawStart : ℕ)
    (hsmall : ∀ m < lawStart,
      1 ≤ UpperCanonical.hlozTransitionCost K m)
    (firstSpec : ∀ t m a, lawStart ≤ m →
      TilingStoppedCoordinateProductSpec
        (favoriteTilingStagePiece t m 1 (firstCreationStage m))
        (firstTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (secondSpec : ∀ t m a, lawStart ≤ m →
      TilingStoppedCoordinateProductSpec
        (favoriteTilingStagePiece t m 2 (firstTransitionEvent t m a))
        (secondTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (thirdSpec : ∀ t m a, lawStart ≤ m →
      TilingStoppedCoordinateProductSpec
        (favoriteTilingStagePiece t m 3 (secondTransitionEvent t m a))
        (screenedThirdTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (hexception : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in Filter.atTop,
      favoriteCount s n ≤ 3 := by
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_path_transition_estimates
      K
  · intro t m a _ha
    by_cases hm : lawStart ≤ m
    · let cert := firstTilingTraceCappedScreenOfStoppedCoordinateSpec
        K t m a (firstSpec t m a hm)
      have hstage : simpleRandomWalk (firstCreationStage m) ≤ 1 := by
        simpa using measure_mono (μ := simpleRandomWalk)
          (subset_univ (firstCreationStage m))
      calc
        simpleRandomWalk (firstTransitionEvent t m a) ≤
            UpperCanonical.hlozTransitionCost K m *
              simpleRandomWalk (firstCreationStage m) :=
          @transition_measure_le_of_traceCappedProductScreening cert.Index
            cert.countableIndex (firstCreationStage m)
            (firstTransitionEvent t m a)
            (measurableSet_firstTransitionEvent t m a)
            (UpperCanonical.hlozTransitionCost K m)
            (HLOZStoppedSpatialScreening.hlozTransitionCost_ne_top K m)
            cert.screening
        _ ≤ UpperCanonical.hlozTransitionCost K m * 1 := by
          simpa only [mul_comm] using
            (mul_le_mul_left hstage (UpperCanonical.hlozTransitionCost K m))
        _ = UpperCanonical.hlozTransitionCost K m := mul_one _
    · have hmeasure : simpleRandomWalk (firstTransitionEvent t m a) ≤ 1 := by
        simpa using measure_mono (μ := simpleRandomWalk)
          (subset_univ (firstTransitionEvent t m a))
      exact hmeasure.trans (hsmall m (Nat.lt_of_not_ge hm))
  · intro t m a _ha
    by_cases hm : lawStart ≤ m
    · let cert := secondTilingTraceCappedScreenOfStoppedCoordinateSpec
        K t m a (secondSpec t m a hm)
      exact @transition_measure_le_of_traceCappedProductScreening cert.Index
        cert.countableIndex (firstTransitionEvent t m a)
        (secondTransitionEvent t m a)
        (measurableSet_secondTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m)
        (HLOZStoppedSpatialScreening.hlozTransitionCost_ne_top K m)
        cert.screening
    · calc
        simpleRandomWalk (secondTransitionEvent t m a) ≤
            simpleRandomWalk (firstTransitionEvent t m a) :=
          measure_mono (secondTransitionEvent_subset_first t m a)
        _ = 1 * simpleRandomWalk (firstTransitionEvent t m a) :=
          (one_mul _).symm
        _ ≤ UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk (firstTransitionEvent t m a) :=
          by simpa only [mul_comm] using
            (mul_le_mul_right (hsmall m (Nat.lt_of_not_ge hm))
              (simpleRandomWalk (firstTransitionEvent t m a)))
  · intro t m a _ha
    by_cases hm : lawStart ≤ m
    · let cert := thirdTilingTraceCappedScreenOfStoppedCoordinateSpec
        K t m a (thirdSpec t m a hm)
      exact @transition_measure_le_of_traceCappedProductScreening cert.Index
        cert.countableIndex (secondTransitionEvent t m a)
        (screenedThirdTransitionEvent t m a)
        (measurableSet_screenedThirdTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m)
        (HLOZStoppedSpatialScreening.hlozTransitionCost_ne_top K m)
        cert.screening
    · have hsub : screenedThirdTransitionEvent t m a ⊆
          secondTransitionEvent t m a := fun _ hs ↦
        thirdTransitionEvent_subset_second t m a hs.1
      calc
        simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
            simpleRandomWalk (secondTransitionEvent t m a) := measure_mono hsub
        _ = 1 * simpleRandomWalk (secondTransitionEvent t m a) :=
          (one_mul _).symm
        _ ≤ UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk (secondTransitionEvent t m a) :=
          by simpa only [mul_comm] using
            (mul_le_mul_right (hsmall m (Nat.lt_of_not_ge hm))
              (simpleRandomWalk (secondTransitionEvent t m a)))
  · exact hexception

end

end Erdos1165.TilingTraceCappedStageAdapter
