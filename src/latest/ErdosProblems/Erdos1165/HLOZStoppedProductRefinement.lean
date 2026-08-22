/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZStoppedSpatialScreening

/-!
# Product screening on trace/favorite-data partitions

The independent product identity (6.7) must be used without conditioning on
the physical threshold-creation clock: fixing that clock also fixes the sum
of the insertion coordinates and replaces the product law by a fixed-sum
law. Thus the creation-time atoms in `HLOZSpatialAdapter` are deliberately
not used here.

Instead, this module packages a countable disjoint partition of the whole
preceding stage by the retained external trace and the fixed favorite data.
The insertion total remains random on each piece. Exact capped product
screens are proved on those pieces and then summed directly to the desired
transition estimate.

The remaining `product_bound` is a bound on the explicit finite sum
`upperProductScreenMass`, and `disintegrate` inside `data` is the literal
capped path/product identity. No path-level transition inequality occurs as
a premise.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZStoppedProductRefinement

open HLOZSpatialAdapter HLOZStoppedSpatialScreening HLOZPathEvents

noncomputable section

/-! ## A sound trace/favorite-data product partition -/

/-- A countable product-law partition of a whole transition stage.

An intended index records the orientation, retained external word, fixed
favorite set, and any earlier-stage branch data, but it does not record the
physical stopping clock or the total number of inserted dominoes. The
`union_piece` field makes this distinction testable: the pieces must cover
the entire preceding stage, not creation-time slices of it. -/
structure TraceUpperProductScreening {Index : Type*} [Countable Index]
    (stage next : Set WalkPath) (cost : ℝ≥0∞) where
  piece : Index → Set WalkPath
  measurable_piece : ∀ z, MeasurableSet (piece z)
  disjoint_piece : Pairwise fun z w ↦ Disjoint (piece z) (piece w)
  union_piece : (⋃ z, piece z) = stage
  next_subset_stage : next ⊆ stage
  data : UpperProductScreenData piece next
  product_bound : FiniteProductScreenBound data cost

/-- Sum the literal product screens over a trace/favorite-data partition.
This is the replacement for summing over physical creation-time atoms. -/
theorem transition_measure_le_of_traceUpperProductScreening
    {Index : Type*} [Countable Index]
    (stage next : Set WalkPath) (hnext : MeasurableSet next)
    (cost : ℝ≥0∞) (hcost : cost ≠ ∞)
    (screening : TraceUpperProductScreening (Index := Index)
      stage next cost) :
    simpleRandomWalk next ≤ cost * simpleRandomWalk stage := by
  have hscreen : AtomwiseRestrictedRealScreen screening.piece next cost :=
    atomwiseRestrictedRealScreen_of_upperProductScreenData
      screening.piece next cost hcost screening.data screening.product_bound
  exact measure_next_le_of_atomwiseTransition screening.piece
    screening.measurable_piece screening.disjoint_piece screening.union_piece
    screening.next_subset_stage
    (pathTransitionDomination_of_atomwiseRestrictedRealScreen
      screening.piece hnext hcost hscreen)

/-- The stage before the first transition, without fixing its physical
creation time. -/
def firstCreationStage (m : ℕ) : Set WalkPath :=
  ⋃ n, thresholdCreationSet m 1 n

/-- A trace partition for the first transition. -/
abbrev FirstTraceProductScreening (Index : Type*) [Countable Index]
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :=
  TraceUpperProductScreening (Index := Index) (firstCreationStage m)
    (firstTransitionEvent t m a) (UpperCanonical.hlozTransitionCost K m)

/-- A trace partition of the complete first-transition event. -/
abbrev SecondTraceProductScreening (Index : Type*) [Countable Index]
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :=
  TraceUpperProductScreening (Index := Index) (firstTransitionEvent t m a)
    (secondTransitionEvent t m a) (UpperCanonical.hlozTransitionCost K m)

/-- A trace partition of the complete second-transition event. -/
abbrev ThirdTraceProductScreening (Index : Type*) [Countable Index]
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :=
  TraceUpperProductScreening (Index := Index) (secondTransitionEvent t m a)
    (screenedThirdTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)

theorem firstTransition_measure_le_of_traceProductScreening
    {Index : Type*} [Countable Index] (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (screening : FirstTraceProductScreening Index K t m a) :
    simpleRandomWalk (firstTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m := by
  have hstage : simpleRandomWalk (firstCreationStage m) ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ (firstCreationStage m))
  calc
    simpleRandomWalk (firstTransitionEvent t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk (firstCreationStage m) :=
      transition_measure_le_of_traceUpperProductScreening
        (firstCreationStage m) (firstTransitionEvent t m a)
        (measurableSet_firstTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m)
        (hlozTransitionCost_ne_top K m) screening
    _ ≤ UpperCanonical.hlozTransitionCost K m * 1 := by
      simpa only [mul_comm] using
        (mul_le_mul_left hstage (UpperCanonical.hlozTransitionCost K m))
    _ = UpperCanonical.hlozTransitionCost K m := mul_one _

theorem secondTransition_measure_le_of_traceProductScreening
    {Index : Type*} [Countable Index] (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (screening : SecondTraceProductScreening Index K t m a) :
    simpleRandomWalk (secondTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (firstTransitionEvent t m a) :=
  transition_measure_le_of_traceUpperProductScreening
    (firstTransitionEvent t m a) (secondTransitionEvent t m a)
    (measurableSet_secondTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (hlozTransitionCost_ne_top K m) screening

theorem screenedThirdTransition_measure_le_of_traceProductScreening
    {Index : Type*} [Countable Index] (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (screening : ThirdTraceProductScreening Index K t m a) :
    simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (secondTransitionEvent t m a) :=
  transition_measure_le_of_traceUpperProductScreening
    (secondTransitionEvent t m a) (screenedThirdTransitionEvent t m a)
    (measurableSet_screenedThirdTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (hlozTransitionCost_ne_top K m) screening

/-- Direct upper-endgame adapter using only trace/favorite-data product
partitions. In particular, none of its inputs conditions on a physical
creation time. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_traceProductScreening
    (K : ℝ≥0)
    (FirstIndex SecondIndex ThirdIndex :
      DominoTiling → ℕ → ((GapScale × GapScale) × GapScale) → Type*)
    [∀ t m a, Countable (FirstIndex t m a)]
    [∀ t m a, Countable (SecondIndex t m a)]
    [∀ t m a, Countable (ThirdIndex t m a)]
    (first : ∀ t m a,
      FirstTraceProductScreening (FirstIndex t m a) K t m a)
    (second : ∀ t m a,
      SecondTraceProductScreening (SecondIndex t m a) K t m a)
    (third : ∀ t m a,
      ThirdTraceProductScreening (ThirdIndex t m a) K t m a)
    (hexception : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in Filter.atTop,
      favoriteCount s n ≤ 3 := by
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_path_transition_estimates
      K
  · intro t m a _
    exact firstTransition_measure_le_of_traceProductScreening
      K t m a (first t m a)
  · intro t m a _
    exact secondTransition_measure_le_of_traceProductScreening
      K t m a (second t m a)
  · intro t m a _
    exact screenedThirdTransition_measure_le_of_traceProductScreening
      K t m a (third t m a)
  · exact hexception

end

end Erdos1165.HLOZStoppedProductRefinement
