/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZPositiveLevelCappedTraceScreening
import ErdosProblems.Erdos1165.HLOZValidFactoredTransitionClosure

/-!
# Valid-support all-six capped trace packages

`TilingValidTraceCappedStageAdapter` partitions only
`stage ∩ validStepWalk`, uses the non-optional tiling trace payload, and
recovers the original transition inequalities from the nullity of
`validStepWalkᶜ`.  This file packages those three supported coordinate laws
over every tiling, mesh point, and sufficiently large level, then connects
them to the upper endgame.  No product certificate is required for the
invalid-walk `Option.none` piece.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZValidSupportCappedTraceScreening

open HLOZPathEvents HLOZPositiveLevelCappedTraceScreening
open HLOZValidFactoredTransitionClosure

noncomputable section

/-- Literal valid-support factored coordinate data at every level. -/
structure AllLevelValidSupportCappedTraceScreenPackage (K : ℝ≥0) where
  data : ∀ t m a, ThreeValidTransitionFactoredCoordinateData K t m a

/-- Literal valid-support factored coordinate data from a positive tail level on.
The finite initial segment is absorbed into the exceptional family. -/
structure PositiveLevelValidSupportCappedTraceScreenPackage
    (start : ℕ) (K : ℝ≥0) where
  start_pos : 0 < start
  data : ∀ t m a, start ≤ m →
    ThreeValidTransitionFactoredCoordinateData K t m a

/-- The three original-event transition inequalities obtained from an
all-level supported package. -/
theorem transition_estimates_of_validSupportPackage
    (K : ℝ≥0) (package : AllLevelValidSupportCappedTraceScreenPackage K) :
    (∀ t m a, simpleRandomWalk (firstTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m) ∧
    (∀ t m a, simpleRandomWalk (secondTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (firstTransitionEvent t m a)) ∧
    (∀ t m a, simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (secondTransitionEvent t m a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t m a
    exact firstTransition_measure_le_of_validFactoredData
      K t m a (package.data t m a)
  · intro t m a
    exact secondTransition_measure_le_of_validFactoredData
      K t m a (package.data t m a)
  · intro t m a
    exact screenedThirdTransition_measure_le_of_validFactoredData
      K t m a (package.data t m a)

/-- All-level valid-support product data imply the eventual upper bound. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_validSupportPackage
    (K : ℝ≥0) (package : AllLevelValidSupportCappedTraceScreenPackage K)
    (hexception : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  obtain ⟨hfirst, hsecond, hthird⟩ :=
    transition_estimates_of_validSupportPackage K package
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_path_transition_estimates
      K
  · intro t m a _
    exact hfirst t m a
  · intro t m a _
    exact hsecond t m a
  · intro t m a _
    exact hthird t m a
  · exact hexception

set_option linter.constructorNameAsVariable false in
/-- Eventual supported screens suffice.  Below `start` the separated-level
events form a finite exceptional prefix; at and above `start`, all three
transition bounds come from the genuine non-optional trace product laws. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_positiveValidSupportPackage
    (start : ℕ) (K : ℝ≥0)
    (package : PositiveLevelValidSupportCappedTraceScreenPackage start K)
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
        exact firstTransition_measure_le_of_validFactoredData
          K t m a (package.data t m a hm)
      · simp [tailFirstTransitionEvent, hm]
    · intro m a _ha
      by_cases hm : start ≤ m
      · simpa [tailSecondTransitionEvent, tailFirstTransitionEvent, hm] using
          secondTransition_measure_le_of_validFactoredData
            K t m a (package.data t m a hm)
      · simp [tailSecondTransitionEvent, tailFirstTransitionEvent, hm]
    · intro m a _ha
      by_cases hm : start ≤ m
      · simpa [tailThirdTransitionEvent, tailSecondTransitionEvent, hm] using
          screenedThirdTransition_measure_le_of_validFactoredData
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

end Erdos1165.HLOZValidSupportCappedTraceScreening
