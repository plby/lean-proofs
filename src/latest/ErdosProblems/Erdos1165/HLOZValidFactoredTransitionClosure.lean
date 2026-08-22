/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.TilingValidTraceCappedStageAdapter
import ErdosProblems.Erdos1165.TilingCappedMarginalization

/-!
# Valid-support transition bounds from literal factored tiling fibres

The valid-support trace adapter requires stopped coordinate product
specifications.  `TilingCappedMarginalization` constructs each such
specification from the literal pointwise distinguished/away factorization.
This file composes the two checked layers for all three HLOZ transitions.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZValidFactoredTransitionClosure

open HLOZPathEvents HLOZStoppedProductRefinement
open TilingCappedMarginalization TilingStoppedProductDisintegration
open TilingValidTraceCappedStageAdapter VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Literal factored stopped-coordinate data on the canonical trace pieces
for all three upper transitions. -/
structure ThreeValidTransitionFactoredCoordinateData
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) where
  first : TilingFactoredStoppedCoordinateData
    (validFavoriteTilingStagePiece t m 1 (firstCreationStage m))
    (firstTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)
  second : TilingFactoredStoppedCoordinateData
    (validFavoriteTilingStagePiece t m 2 (firstTransitionEvent t m a))
    (secondTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)
  third : TilingFactoredStoppedCoordinateData
    (validFavoriteTilingStagePiece t m 3 (secondTransitionEvent t m a))
    (screenedThirdTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)

/-- Marginalize the distinguished coordinates in each literal factored
fibre, yielding the exact valid-support specifications. -/
noncomputable def threeValidTransitionStoppedSpecsOfFactoredData
    {K : ℝ≥0} {t : DominoTiling} {m : ℕ}
    {a : (GapScale × GapScale) × GapScale}
    (data : ThreeValidTransitionFactoredCoordinateData K t m a) :
    ThreeValidTransitionStoppedCoordinateSpecs K t m a where
  first := tilingStoppedCoordinateProductSpecOfFactoredData data.first
  second := tilingStoppedCoordinateProductSpecOfFactoredData data.second
  third := tilingStoppedCoordinateProductSpecOfFactoredData data.third

/-- The first transition bound from literal factored stopped fibres. -/
theorem firstTransition_measure_le_of_validFactoredData
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (data : ThreeValidTransitionFactoredCoordinateData K t m a) :
    simpleRandomWalk (firstTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m :=
  firstTransition_measure_le_of_validStoppedSpecs K t m a
    (threeValidTransitionStoppedSpecsOfFactoredData data)

/-- The second transition bound from literal factored stopped fibres. -/
theorem secondTransition_measure_le_of_validFactoredData
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (data : ThreeValidTransitionFactoredCoordinateData K t m a) :
    simpleRandomWalk (secondTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (firstTransitionEvent t m a) :=
  secondTransition_measure_le_of_validStoppedSpecs K t m a
    (threeValidTransitionStoppedSpecsOfFactoredData data)

/-- The screened third transition bound from literal factored stopped
fibres. -/
theorem screenedThirdTransition_measure_le_of_validFactoredData
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (data : ThreeValidTransitionFactoredCoordinateData K t m a) :
    simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (secondTransitionEvent t m a) :=
  screenedThirdTransition_measure_le_of_validStoppedSpecs K t m a
    (threeValidTransitionStoppedSpecsOfFactoredData data)

/-- Compact package of the three transition estimates. -/
theorem threeTransition_bounds_of_validFactoredData
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (data : ThreeValidTransitionFactoredCoordinateData K t m a) :
    simpleRandomWalk (firstTransitionEvent t m a) ≤
        UpperCanonical.hlozTransitionCost K m ∧
      simpleRandomWalk (secondTransitionEvent t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk (firstTransitionEvent t m a) ∧
      simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk (secondTransitionEvent t m a) := by
  exact ⟨firstTransition_measure_le_of_validFactoredData K t m a data,
    secondTransition_measure_le_of_validFactoredData K t m a data,
    screenedThirdTransition_measure_le_of_validFactoredData K t m a data⟩

end

end Erdos1165.HLOZValidFactoredTransitionClosure
