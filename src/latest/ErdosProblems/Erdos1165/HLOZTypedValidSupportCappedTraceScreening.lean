import ErdosProblems.Erdos1165.TilingTypedTransitionFactorization
import ErdosProblems.Erdos1165.TilingTypedCapCoherence
import ErdosProblems.Erdos1165.HLOZPositiveLevelCappedTraceScreening

/-!
# Positive-level upper screening from typed retained traces

This module packages the literal all-six stopped-coordinate laws built on
`TypedFavoriteTilingTraceCode`.  The package begins above level one, exactly
where the stopped-fibre invariance theorem applies.  Smaller levels are put
into the finite exceptional prefix; in particular, no level-zero geometric
balance or product law is asserted.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZTypedValidSupportCappedTraceScreening

open HLOZPathEvents HLOZPositiveLevelCappedTraceScreening
open HLOZStoppedProductRefinement HLOZTracePartitionAdapter
open TilingTypedTransitionFactorization
open TilingTypedCapCoherence
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Literal typed retained-trace product data from a level strictly larger
than one onward. -/
structure PositiveLevelTypedFactoredCoordinatePackage
    (start : ℕ) (K : ℝ≥0) where
  one_lt_start : 1 < start
  data : ∀ t m a, start ≤ m →
    ThreeTypedTransitionFactoredCoordinateData K t m a

/-- Assemble the eventual typed package from the three finite away-total
screens.  All stopped spatial and favorite-history fields are supplied by
the constructors in `TilingTypedTransitionFactorization`. -/
noncomputable def positiveLevelTypedFactoredCoordinatePackageOfScreens
    (start : ℕ) (K : ℝ≥0) (hstart : 1 < start)
    (first : ∀ t m a, start ≤ m →
      TypedFiniteAwayScreenData t m 1 (firstCreationStage m)
        (firstTransitionEvent t m a ∩ validStepWalk)
        (UpperCanonical.hlozTransitionCost K m))
    (second : ∀ t m a, start ≤ m →
      TypedFiniteAwayScreenData t m 2 (firstTransitionEvent t m a)
        (secondTransitionEvent t m a ∩ validStepWalk)
        (UpperCanonical.hlozTransitionCost K m))
    (third : ∀ t m a, start ≤ m →
      TypedFiniteAwayScreenData t m 3 (secondTransitionEvent t m a)
        (screenedThirdTransitionEvent t m a ∩ validStepWalk)
        (UpperCanonical.hlozTransitionCost K m)) :
    PositiveLevelTypedFactoredCoordinatePackage start K where
  one_lt_start := hstart
  data t m a hm := threeTypedTransitionFactoredCoordinateDataOfScreens
    K t m (hstart.trans_le hm) a
    (first t m a hm) (second t m a hm) (third t m a hm)

/-- Assemble the eventual package from screens on natural-valued away
totals.  Their auxiliary-cap monotonicity is automatic. -/
noncomputable def
    positiveLevelTypedFactoredCoordinatePackageOfCapIndependentScreens
    (start : ℕ) (K : ℝ≥0) (hstart : 1 < start)
    (first : ∀ t m a, start ≤ m →
      TypedCapIndependentAwayScreenData t m 1 (firstCreationStage m)
        (firstTransitionEvent t m a ∩ validStepWalk)
        (UpperCanonical.hlozTransitionCost K m))
    (second : ∀ t m a, start ≤ m →
      TypedCapIndependentAwayScreenData t m 2 (firstTransitionEvent t m a)
        (secondTransitionEvent t m a ∩ validStepWalk)
        (UpperCanonical.hlozTransitionCost K m))
    (third : ∀ t m a, start ≤ m →
      TypedCapIndependentAwayScreenData t m 3 (secondTransitionEvent t m a)
        (screenedThirdTransitionEvent t m a ∩ validStepWalk)
        (UpperCanonical.hlozTransitionCost K m)) :
    PositiveLevelTypedFactoredCoordinatePackage start K :=
  positiveLevelTypedFactoredCoordinatePackageOfScreens start K hstart
    (fun t m a hm ↦ (first t m a hm).toFiniteAwayScreenData)
    (fun t m a hm ↦ (second t m a hm).toFiniteAwayScreenData)
    (fun t m a hm ↦ (third t m a hm).toFiniteAwayScreenData)

set_option linter.constructorNameAsVariable false in
/-- The HLOZ upper endgame from the literal typed retained-trace laws on an
eventual level tail.  The finitely many smaller levels are absorbed into
`positiveLevelExceptionalEvent`. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_typedPackage
    (start : ℕ) (K : ℝ≥0)
    (package : PositiveLevelTypedFactoredCoordinatePackage start K)
    (hexception : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
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
      · rw [tailFirstTransitionEvent, if_pos hm]
        exact firstTransition_measure_le_of_typedFactoredData
          K t m a (package.data t m a hm)
      · simp [tailFirstTransitionEvent, hm]
    · intro m a _ha
      by_cases hm : start ≤ m
      · simpa [tailSecondTransitionEvent, tailFirstTransitionEvent, hm] using
          secondTransition_measure_le_of_typedFactoredData
            K t m a (package.data t m a hm)
      · simp [tailSecondTransitionEvent, tailFirstTransitionEvent, hm]
    · intro m a _ha
      by_cases hm : start ≤ m
      · simpa [tailThirdTransitionEvent, tailSecondTransitionEvent, hm] using
          screenedThirdTransition_measure_le_of_typedFactoredData
            K t m a (package.data t m a hm)
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

end Erdos1165.HLOZTypedValidSupportCappedTraceScreening
