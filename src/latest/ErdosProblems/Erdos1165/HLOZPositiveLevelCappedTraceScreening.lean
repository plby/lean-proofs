import ErdosProblems.Erdos1165.TilingTraceCappedStageAdapter

/-!
# Positive-level capped trace screens

The geometric and favorite-level product laws require a positive level.
This module gives the sound endgame interface: screens are supplied only
from a positive start level onward, and the finitely many smaller levels are
absorbed into the exceptional family.  No artificial `m = 0` product law is
required.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace Erdos1165.HLOZPositiveLevelCappedTraceScreening

open HLOZPathEvents HLOZTraceCappedProductScreening
open HLOZStoppedSpatialScreening
open HLOZStoppedProductRefinement
open TilingStoppedProductDisintegration TilingVariableStoppedTracePartition
open TilingTraceCappedStageAdapter

noncomputable section

/-- All-six trace screens beginning at one positive level. -/
structure PositiveLevelCappedTraceScreenPackage (start : ℕ) (K : ℝ≥0) where
  start_pos : 0 < start
  screens : ∀ t m a, start ≤ m → ThreeTransitionCappedTraceScreens K t m a

/-- Assemble positive-level all-six stopped-coordinate specifications into
the sound positive-level package. -/
def positiveLevelCappedTraceScreenPackageOfTilingStoppedCoordinateSpecs
    (start : ℕ) (hstart : 0 < start) (K : ℝ≥0)
    (firstSpec : ∀ t m a, start ≤ m →
      TilingStoppedCoordinateProductSpec
        (favoriteTilingStagePiece t m 1 (firstCreationStage m))
        (firstTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (secondSpec : ∀ t m a, start ≤ m →
      TilingStoppedCoordinateProductSpec
        (favoriteTilingStagePiece t m 2 (firstTransitionEvent t m a))
        (secondTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (thirdSpec : ∀ t m a, start ≤ m →
      TilingStoppedCoordinateProductSpec
        (favoriteTilingStagePiece t m 3 (secondTransitionEvent t m a))
        (screenedThirdTransitionEvent t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    PositiveLevelCappedTraceScreenPackage start K where
  start_pos := hstart
  screens t m a hm := {
    first := firstTilingTraceCappedScreenOfStoppedCoordinateSpec
      K t m a (firstSpec t m a hm)
    second := secondTilingTraceCappedScreenOfStoppedCoordinateSpec
      K t m a (secondSpec t m a hm)
    third := thirdTilingTraceCappedScreenOfStoppedCoordinateSpec
      K t m a (thirdSpec t m a hm) }

def tailFirstTransitionEvent (start : ℕ) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) : Set WalkPath :=
  if start ≤ m then firstTransitionEvent t m a else ∅

def tailSecondTransitionEvent (start : ℕ) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) : Set WalkPath :=
  if start ≤ m then secondTransitionEvent t m a else ∅

def tailThirdTransitionEvent (start : ℕ) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) : Set WalkPath :=
  if start ≤ m then screenedThirdTransitionEvent t m a else ∅

/-- The original exceptional event plus the finite prefix of screened level
events below `start`. -/
def positiveLevelExceptionalEvent (start : ℕ) (t : DominoTiling) (m : ℕ) :
    Set WalkPath :=
  hlozExceptionalEvent t m ∪
    if m < start then hlozSeparatedLevelEvent t m else ∅

theorem positiveLevel_screened_mesh_cover (start : ℕ)
    (t : DominoTiling) (m : ℕ) :
    hlozSeparatedLevelEvent t m ⊆
      positiveLevelExceptionalEvent start t m ∪
        UpperAssembly.meshBranchUnion properGapMesh
          (tailThirdTransitionEvent start t m) := by
  by_cases hm : start ≤ m
  · have htail : tailThirdTransitionEvent start t m =
        screenedThirdTransitionEvent t m := by
      funext a
      simp [tailThirdTransitionEvent, hm]
    rw [positiveLevelExceptionalEvent,
      if_neg (Nat.not_lt_of_ge hm), union_empty, htail]
    exact hlozSeparatedLevelEvent_screened_mesh_cover t m
  · have hlt : m < start := Nat.lt_of_not_ge hm
    intro s hs
    left
    exact Or.inr (by simpa [hlt] using hs)

theorem positiveLevelExceptional_series_ne_top
    (start : ℕ) (t : DominoTiling)
    (hexception : ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞) :
    ∑' m, simpleRandomWalk (positiveLevelExceptionalEvent start t m) ≠ ∞ := by
  let small : ℕ → ℝ≥0∞ := fun m ↦
    if m < start then simpleRandomWalk (hlozSeparatedLevelEvent t m) else 0
  have hsmall : ∑' m, small m ≠ ∞ := by
    rw [tsum_eq_sum (s := Finset.range start)]
    · apply ENNReal.sum_ne_top.mpr
      intro m hm
      have hlt : m < start := Finset.mem_range.mp hm
      simp only [small, if_pos hlt]
      exact measure_ne_top _ _
    · intro m hm
      have hnot : ¬m < start := by simpa [Finset.mem_range] using hm
      simp [small, hnot]
  have hpoint : ∀ m,
      simpleRandomWalk (positiveLevelExceptionalEvent start t m) ≤
        simpleRandomWalk (hlozExceptionalEvent t m) + small m := by
    intro m
    refine (measure_union_le _ _).trans ?_
    change simpleRandomWalk (hlozExceptionalEvent t m) +
        simpleRandomWalk
          (if m < start then hlozSeparatedLevelEvent t m else ∅) ≤ _
    unfold small
    by_cases hm : m < start <;> simp [hm]
  have hmajor :
      ∑' m, (simpleRandomWalk (hlozExceptionalEvent t m) + small m) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hexception, hsmall⟩
  exact ne_top_of_le_ne_top hmajor (ENNReal.tsum_le_tsum hpoint)

set_option linter.constructorNameAsVariable false in
/-- The HLOZ upper endgame from product screens only at positive, sufficiently
large levels.  Small levels are a finite exceptional prefix. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_positiveLevelPackage
    (start : ℕ) (K : ℝ≥0)
    (package : PositiveLevelCappedTraceScreenPackage start K)
    (hexception : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop,
      favoriteCount s n ≤ 3 := by
  have hscreened : ∀ t,
      ∑' m, simpleRandomWalk (hlozSeparatedLevelEvent t m) ≠ ∞ := by
    intro t
    apply UpperAssembly.screenedLevel_series_ne_top simpleRandomWalk properGapMesh
      (hlozSeparatedLevelEvent t) (positiveLevelExceptionalEvent start t)
      (tailFirstTransitionEvent start t)
      (tailSecondTransitionEvent start t)
      (tailThirdTransitionEvent start t)
      (UpperCanonical.hlozTransitionCost K) (K ^ 3)
      (3 * ScreeningInstantiation.kappa)
    · exact ScreeningInstantiation.hloz_parameter_inequalities.2.2.2.2.2.2.2.1
    · exact positiveLevel_screened_mesh_cover start t
    · intro m a _ha
      by_cases hm : start ≤ m
      · let cert := (package.screens t m a hm).first
        have hstage : simpleRandomWalk (firstCreationStage m) ≤ 1 := by
          simpa using measure_mono (μ := simpleRandomWalk)
            (subset_univ (firstCreationStage m))
        rw [tailFirstTransitionEvent, if_pos hm]
        calc
          simpleRandomWalk (firstTransitionEvent t m a) ≤
              UpperCanonical.hlozTransitionCost K m *
                simpleRandomWalk (firstCreationStage m) :=
            @transition_measure_le_of_traceCappedProductScreening cert.Index
              cert.countableIndex (firstCreationStage m)
              (firstTransitionEvent t m a)
              (measurableSet_firstTransitionEvent t m a)
              (UpperCanonical.hlozTransitionCost K m)
              (hlozTransitionCost_ne_top K m) cert.screening
          _ ≤ UpperCanonical.hlozTransitionCost K m * 1 := by
            simpa only [mul_comm] using
              (mul_le_mul_left hstage (UpperCanonical.hlozTransitionCost K m))
          _ = UpperCanonical.hlozTransitionCost K m := mul_one _
      · simp [tailFirstTransitionEvent, hm]
    · intro m a _ha
      by_cases hm : start ≤ m
      · let screens := package.screens t m a hm
        let cert := screens.second
        simpa [tailSecondTransitionEvent, tailFirstTransitionEvent, hm] using
          (@transition_measure_le_of_traceCappedProductScreening cert.Index
            cert.countableIndex (firstTransitionEvent t m a)
            (secondTransitionEvent t m a)
            (measurableSet_secondTransitionEvent t m a)
            (UpperCanonical.hlozTransitionCost K m)
            (hlozTransitionCost_ne_top K m) cert.screening)
      · simp [tailSecondTransitionEvent, tailFirstTransitionEvent, hm]
    · intro m a _ha
      by_cases hm : start ≤ m
      · let screens := package.screens t m a hm
        let cert := screens.third
        simpa [tailThirdTransitionEvent, tailSecondTransitionEvent, hm] using
          (@transition_measure_le_of_traceCappedProductScreening cert.Index
            cert.countableIndex (secondTransitionEvent t m a)
            (screenedThirdTransitionEvent t m a)
            (measurableSet_screenedThirdTransitionEvent t m a)
            (UpperCanonical.hlozTransitionCost K m)
            (hlozTransitionCost_ne_top K m) cert.screening)
      · simp [tailThirdTransitionEvent, tailSecondTransitionEvent, hm]
    · exact positiveLevelExceptional_series_ne_top start t (hexception t)
    · intro m
      exact (UpperCanonical.hlozTransitionCost_cube K m).le
  have hsum : ∑' m, simpleRandomWalk (levelFavoriteSet m 4) ≠ ∞ :=
    level_event_summable_of_six_tilings simpleRandomWalk
      levelFavoriteSet_four_subset_six_hloz_tilings hscreened
  exact UpperAssembly.ae_eventually_favoriteCount_le_three_of_M4_summable
    simpleRandomWalk hsum simpleRandomWalk_maxLocalTime_tendsto

end

end Erdos1165.HLOZPositiveLevelCappedTraceScreening
