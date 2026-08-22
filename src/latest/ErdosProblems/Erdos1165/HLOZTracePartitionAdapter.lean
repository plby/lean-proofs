/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZTraceScreenPackage
import ErdosProblems.Erdos1165.VariableStoppedTracePartition

/-!
# Restricting variable stopped-trace partitions to transition stages

The variable creation fibres partition every rank-`k` reaching stage without
recording the physical creation time.  Intersecting those pieces with a
measurable preceding transition stage gives the exact partitions needed by
the three product screens.  This file discharges all of that deterministic
partition bookkeeping; the remaining data are literal capped product
disintegrations and their finite product bounds.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZTracePartitionAdapter

open HLOZPathEvents HLOZStoppedProductRefinement HLOZStoppedSpatialScreening
open HLOZTraceScreenPackage VariableStoppedTracePartition
open LazyDecomposition

noncomputable section

/-- A variable stopped-trace piece restricted to the actual preceding
transition stage. -/
def favoriteStagePiece (o : Orientation) (m k : ℕ)
    (stage : Set WalkPath) (z : FavoriteTraceCode o) : Set WalkPath :=
  favoriteCreationPiece m k z ∩ stage

theorem measurableSet_favoriteStagePiece (o : Orientation) (m k : ℕ)
    {stage : Set WalkPath} (hstage : MeasurableSet stage)
    (z : FavoriteTraceCode o) :
    MeasurableSet (favoriteStagePiece o m k stage z) :=
  (measurableSet_favoriteCreationPiece m k z).inter hstage

theorem disjoint_favoriteStagePiece_of_ne (o : Orientation) (m k : ℕ)
    (stage : Set WalkPath) {z w : FavoriteTraceCode o} (hzw : z ≠ w) :
    Disjoint (favoriteStagePiece o m k stage z)
      (favoriteStagePiece o m k stage w) :=
  (disjoint_favoriteCreationPiece_of_ne m k hzw).mono
    inter_subset_left inter_subset_left

theorem iUnion_favoriteStagePiece (o : Orientation) (m k : ℕ)
    {stage : Set WalkPath} (hstage : stage ⊆ thresholdReachStage m k) :
    (⋃ z : FavoriteTraceCode o, favoriteStagePiece o m k stage z) = stage := by
  ext s
  constructor
  · rintro hs
    rcases Set.mem_iUnion.mp hs with ⟨z, _hz, hstageMem⟩
    exact hstageMem
  · intro hs
    have hreach : s ∈ thresholdReachStage m k := hstage hs
    rw [← iUnion_favoriteCreationPiece (o := o) m k] at hreach
    rcases Set.mem_iUnion.mp hreach with ⟨z, hz⟩
    exact Set.mem_iUnion.mpr ⟨z, hz, hs⟩

/-- Populate all structural fields of an existential trace product screen
from the literal variable stopped-trace partition.  Only the finite capped
product data and its explicit numerical bound remain as inputs. -/
def someTraceUpperProductScreeningOfFavoriteStage
    (o : Orientation) (m k : ℕ) (stage next : Set WalkPath)
    (cost : ℝ≥0∞) (hstageMeasurable : MeasurableSet stage)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hnext : next ⊆ stage)
    (data : UpperProductScreenData
      (favoriteStagePiece o m k stage) next)
    (hbound : FiniteProductScreenBound data cost) :
    SomeTraceUpperProductScreening stage next cost where
  Index := FavoriteTraceCode o
  countableIndex := inferInstance
  screening := {
    piece := favoriteStagePiece o m k stage
    measurable_piece := measurableSet_favoriteStagePiece o m k
      hstageMeasurable
    disjoint_piece := fun _z _w hzw ↦
      disjoint_favoriteStagePiece_of_ne o m k stage hzw
    union_piece := iUnion_favoriteStagePiece o m k hstage
    next_subset_stage := hnext
    data := data
    product_bound := hbound }

theorem firstTransitionEvent_subset_thresholdReachStage_one
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    firstTransitionEvent t m a ⊆ thresholdReachStage m 1 := by
  intro s hs
  simp only [firstTransitionEvent, Set.mem_iUnion] at hs
  rcases hs with ⟨n₁, n₂, hs⟩
  rw [thresholdReachStage_eq_iUnion_creation]
  exact Set.mem_iUnion.mpr ⟨n₁, hs.1⟩

theorem firstTransitionEvent_subset_thresholdReachStage_two
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    firstTransitionEvent t m a ⊆ thresholdReachStage m 2 := by
  intro s hs
  simp only [firstTransitionEvent, Set.mem_iUnion] at hs
  rcases hs with ⟨n₁, n₂, hs⟩
  rw [thresholdReachStage_eq_iUnion_creation]
  exact Set.mem_iUnion.mpr ⟨n₂, hs.2.1⟩

theorem secondTransitionEvent_subset_thresholdReachStage_three
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    secondTransitionEvent t m a ⊆ thresholdReachStage m 3 := by
  intro s hs
  simp only [secondTransitionEvent, Set.mem_iUnion] at hs
  rcases hs with ⟨n₁, n₂, n₃, hs⟩
  rw [thresholdReachStage_eq_iUnion_creation]
  exact Set.mem_iUnion.mpr ⟨n₃, hs.2.2.1⟩

/-- The first variable-trace partition with all deterministic fields closed. -/
def firstTraceScreenOfProductData (o : Orientation) (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (data : UpperProductScreenData
      (favoriteStagePiece o m 1 (firstCreationStage m))
      (firstTransitionEvent t m a))
    (hbound : FiniteProductScreenBound data
      (UpperCanonical.hlozTransitionCost K m)) :
    SomeTraceUpperProductScreening (firstCreationStage m)
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
  exact someTraceUpperProductScreeningOfFavoriteStage o m 1
    (firstCreationStage m) (firstTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m) hstageMeasurable hstage hnext
    data hbound

/-- The second variable-trace partition with all deterministic fields closed. -/
def secondTraceScreenOfProductData (o : Orientation) (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (data : UpperProductScreenData
      (favoriteStagePiece o m 2 (firstTransitionEvent t m a))
      (secondTransitionEvent t m a))
    (hbound : FiniteProductScreenBound data
      (UpperCanonical.hlozTransitionCost K m)) :
    SomeTraceUpperProductScreening (firstTransitionEvent t m a)
      (secondTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m) := by
  exact someTraceUpperProductScreeningOfFavoriteStage o m 2
    (firstTransitionEvent t m a) (secondTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (measurableSet_firstTransitionEvent t m a)
    (firstTransitionEvent_subset_thresholdReachStage_two t m a)
    (secondTransitionEvent_subset_first t m a) data hbound

/-- The third variable-trace partition with all deterministic fields closed. -/
def thirdTraceScreenOfProductData (o : Orientation) (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (data : UpperProductScreenData
      (favoriteStagePiece o m 3 (secondTransitionEvent t m a))
      (screenedThirdTransitionEvent t m a))
    (hbound : FiniteProductScreenBound data
      (UpperCanonical.hlozTransitionCost K m)) :
    SomeTraceUpperProductScreening (secondTransitionEvent t m a)
      (screenedThirdTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m) := by
  have hnext : screenedThirdTransitionEvent t m a ⊆
      secondTransitionEvent t m a := by
    intro s hs
    exact thirdTransitionEvent_subset_second t m a hs.1
  exact someTraceUpperProductScreeningOfFavoriteStage o m 3
    (secondTransitionEvent t m a) (screenedThirdTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (measurableSet_secondTransitionEvent t m a)
    (secondTransitionEvent_subset_thresholdReachStage_three t m a)
    hnext data hbound

/-! ## All-level assembly from literal product data -/

/-- Assemble the compact all-level certificate from the three families of
literal capped product disintegrations and their explicit finite bounds.
Each transition may choose its deletion orientation independently. -/
def allLevelTraceScreenPackageOfProductData (K : ℝ≥0)
    (firstOrientation secondOrientation thirdOrientation :
      DominoTiling → ℕ → ((GapScale × GapScale) × GapScale) → Orientation)
    (firstData : ∀ t m a,
      UpperProductScreenData
        (favoriteStagePiece (firstOrientation t m a) m 1
          (firstCreationStage m))
        (firstTransitionEvent t m a))
    (firstBound : ∀ t m a,
      FiniteProductScreenBound (firstData t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (secondData : ∀ t m a,
      UpperProductScreenData
        (favoriteStagePiece (secondOrientation t m a) m 2
          (firstTransitionEvent t m a))
        (secondTransitionEvent t m a))
    (secondBound : ∀ t m a,
      FiniteProductScreenBound (secondData t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (thirdData : ∀ t m a,
      UpperProductScreenData
        (favoriteStagePiece (thirdOrientation t m a) m 3
          (secondTransitionEvent t m a))
        (screenedThirdTransitionEvent t m a))
    (thirdBound : ∀ t m a,
      FiniteProductScreenBound (thirdData t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    AllLevelTraceScreenPackage K where
  screens t m a := {
    first := firstTraceScreenOfProductData (firstOrientation t m a) K t m a
      (firstData t m a) (firstBound t m a)
    second := secondTraceScreenOfProductData (secondOrientation t m a) K t m a
      (secondData t m a) (secondBound t m a)
    third := thirdTraceScreenOfProductData (thirdOrientation t m a) K t m a
      (thirdData t m a) (thirdBound t m a) }

/-- Direct upper endgame whose only spatial inputs are the literal product
data and their checked finite product bounds. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_productData
    (K : ℝ≥0)
    (firstOrientation secondOrientation thirdOrientation :
      DominoTiling → ℕ → ((GapScale × GapScale) × GapScale) → Orientation)
    (firstData : ∀ t m a,
      UpperProductScreenData
        (favoriteStagePiece (firstOrientation t m a) m 1
          (firstCreationStage m))
        (firstTransitionEvent t m a))
    (firstBound : ∀ t m a,
      FiniteProductScreenBound (firstData t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (secondData : ∀ t m a,
      UpperProductScreenData
        (favoriteStagePiece (secondOrientation t m a) m 2
          (firstTransitionEvent t m a))
        (secondTransitionEvent t m a))
    (secondBound : ∀ t m a,
      FiniteProductScreenBound (secondData t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (thirdData : ∀ t m a,
      UpperProductScreenData
        (favoriteStagePiece (thirdOrientation t m a) m 3
          (secondTransitionEvent t m a))
        (screenedThirdTransitionEvent t m a))
    (thirdBound : ∀ t m a,
      FiniteProductScreenBound (thirdData t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (hexception : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in Filter.atTop,
      favoriteCount s n ≤ 3 := by
  exact simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_package K
    (allLevelTraceScreenPackageOfProductData K firstOrientation
      secondOrientation thirdOrientation firstData firstBound secondData
      secondBound thirdData thirdBound)
    hexception

end

end Erdos1165.HLOZTracePartitionAdapter
