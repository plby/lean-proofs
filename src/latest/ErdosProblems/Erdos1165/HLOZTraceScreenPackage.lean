/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZStoppedProductRefinement

/-!
# Existential packages for the three trace-product screens

The sound stopped product partition may use a different countable trace code
at every transition, tiling, level, and mesh point.  This file hides those
index choices and exposes the compact all-level input needed by the upper
endgame.  No physical threshold-creation time is part of an index.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos1165.HLOZTraceScreenPackage

open HLOZPathEvents HLOZStoppedProductRefinement

noncomputable section

/-- A trace product screen with an existentially chosen countable index. -/
structure SomeTraceUpperProductScreening
    (stage next : Set WalkPath) (cost : ℝ≥0∞) where
  Index : Type
  countableIndex : Countable Index
  screening : @TraceUpperProductScreening Index countableIndex stage next cost

/-- All three sound trace/favorite-data product screens at one level and one
mesh point.  The index types are independent, as they are in the literal
stopped disintegrations. -/
structure ThreeTransitionTraceScreens (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) where
  first : SomeTraceUpperProductScreening (firstCreationStage m)
    (firstTransitionEvent t m a) (UpperCanonical.hlozTransitionCost K m)
  second : SomeTraceUpperProductScreening (firstTransitionEvent t m a)
    (secondTransitionEvent t m a) (UpperCanonical.hlozTransitionCost K m)
  third : SomeTraceUpperProductScreening (secondTransitionEvent t m a)
    (screenedThirdTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)

/-- Compact all-level certificate.  Each field may choose its trace index
existentially and independently. -/
structure AllLevelTraceScreenPackage (K : ℝ≥0) where
  screens : ∀ t m a, ThreeTransitionTraceScreens K t m a

theorem firstTransition_measure_le_of_package (K : ℝ≥0)
    (package : AllLevelTraceScreenPackage K) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    simpleRandomWalk (firstTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m := by
  let cert := (package.screens t m a).first
  exact @firstTransition_measure_le_of_traceProductScreening cert.Index
    cert.countableIndex K t m a cert.screening

theorem secondTransition_measure_le_of_package (K : ℝ≥0)
    (package : AllLevelTraceScreenPackage K) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    simpleRandomWalk (secondTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (firstTransitionEvent t m a) := by
  let cert := (package.screens t m a).second
  exact @secondTransition_measure_le_of_traceProductScreening cert.Index
    cert.countableIndex K t m a cert.screening

theorem screenedThirdTransition_measure_le_of_package (K : ℝ≥0)
    (package : AllLevelTraceScreenPackage K) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (secondTransitionEvent t m a) := by
  let cert := (package.screens t m a).third
  exact @screenedThirdTransition_measure_le_of_traceProductScreening cert.Index
    cert.countableIndex K t m a cert.screening

/-- The upper endgame from one compact trace-screen package and the summable
exceptional family. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_package
    (K : ℝ≥0) (package : AllLevelTraceScreenPackage K)
    (hexception : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in Filter.atTop,
      favoriteCount s n ≤ 3 := by
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_path_transition_estimates
      K
  · intro t m a _
    exact firstTransition_measure_le_of_package K package t m a
  · intro t m a _
    exact secondTransition_measure_le_of_package K package t m a
  · intro t m a _
    exact screenedThirdTransition_measure_le_of_package K package t m a
  · exact hexception

end

end Erdos1165.HLOZTraceScreenPackage
