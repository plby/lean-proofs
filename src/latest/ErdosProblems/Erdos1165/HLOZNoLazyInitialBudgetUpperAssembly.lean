/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZNoLazyDirectSeriesEndgame
import ErdosProblems.Erdos1165.HLOZNoLazyFullGapSeriesAssembly
import ErdosProblems.Erdos1165.HLOZNoLazyInitialBudgetMixedTransitionFactors

/-!
# Internal upper assembly for fixed-first-strip low factors

This module performs the carrier-independent final wiring for the corrected
no-lazy transition chain.  It constructs the six heterogeneous factor
packages from literal mesh-creation data and invokes the direct-series
endgame.

The theorem here is deliberately intermediate: the final source carrier
constructs the exceptional and rank-majorant series before calling it.  No
factor package, transition inequality, gap-Harnack hypothesis, or lazy-event
series is exposed.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZNoLazyInitialBudgetUpperAssembly

open HLOZNoLazyDirectSeriesEndgame
open HLOZNoLazyFullBetaProductBranch HLOZNoLazyFullGapSeriesAssembly
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZPathEvents HLOZRawFullGapProductPromotion
open HLOZSourceCorrectFullGapClosure

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple

/-- Internal endgame with the corrected factor construction fixed.

`low` contains only literal stopped-candidate/mesh-creation data and its
Prop. 4.9 ratio envelope; all high and low transition costs are closed by
the constructors imported above.  The series arguments are exactly the
outputs of the source/Theta rank-majorant layer and the no-lazy full-gap
series assembly. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_initialBudget_rank_series
    (product : FullBetaSourceCorrectAllTilingProductData)
    (low : ∀ t : DominoTiling,
      PositiveLevelNoLazyInitialBudgetMeshCreationData
        (firstRawStagedCandidate product)
        (secondRawStagedCandidate product)
        (thirdRawStagedCandidate product) t)
    (hbase : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (major₁ major₂ major₃ : DominoTiling → ℕ → Set WalkPath)
    (hsubset₁ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        firstRawStagedCandidate product t m a ⊆ major₁ t m)
    (hsubset₂ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        secondRawStagedCandidate product t m a ⊆ major₂ t m)
    (hsubset₃ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        thirdRawStagedCandidate product t m a ⊆ major₃ t m)
    (hmajor₁ : ∀ t, ∑' m, simpleRandomWalk (major₁ t m) ≠ ∞)
    (hmajor₂ : ∀ t, ∑' m, simpleRandomWalk (major₂ t m) ≠ ∞)
    (hmajor₃ : ∀ t, ∑' m, simpleRandomWalk (major₃ t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_noLazy_factors_and_rank_majorants
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product) 1
      (rawProperNoLazyInitialBudgetMixedPackagesOfMeshCreation product low)
      hbase major₁ major₂ major₃
  · exact hsubset₁
  · exact hsubset₂
  · exact hsubset₃
  · exact hmajor₁
  · exact hmajor₂
  · exact hmajor₃

/-- Internal source-series specialization.  The HLOZ exceptional series is
constructed from the three candidate-local oriented source series and the
literal low-external complement, using the planar maximum lower deviation
only for the already identified late terms. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_initialBudget_source_series
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (product : FullBetaSourceCorrectAllTilingProductData)
    (low : ∀ t : DominoTiling,
      PositiveLevelNoLazyInitialBudgetMeshCreationData
        (firstRawStagedCandidate product)
        (secondRawStagedCandidate product)
        (thirdRawStagedCandidate product) t)
    (hbalance : ∀ t, ∑' m, simpleRandomWalk
      (candidateLocalProductPositiveInterfaceBalanceRemainderEvent
        product t m) ≠ ∞)
    (hsourceOne : ∀ t, ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank product t 1 m) ≠ ∞)
    (hsourceTwo : ∀ t, ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank product t 2 m) ≠ ∞)
    (hsourceThree : ∀ t, ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank product t 3 m) ≠ ∞)
    (hcomplement : ∀ t, ∑' m, simpleRandomWalk
      (onTimeProductBetaCandidateLocalComplementEvent t m
        (product.externalThreshold m)) ≠ ∞)
    (major₁ major₂ major₃ : DominoTiling → ℕ → Set WalkPath)
    (hsubset₁ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        firstRawStagedCandidate product t m a ⊆ major₁ t m)
    (hsubset₂ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        secondRawStagedCandidate product t m a ⊆ major₂ t m)
    (hsubset₃ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        thirdRawStagedCandidate product t m a ⊆ major₃ t m)
    (hmajor₁ : ∀ t, ∑' m, simpleRandomWalk (major₁ t m) ≠ ∞)
    (hmajor₂ : ∀ t, ∑' m, simpleRandomWalk (major₂ t m) ≠ ∞)
    (hmajor₃ : ∀ t, ∑' m, simpleRandomWalk (major₃ t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_initialBudget_rank_series
      product low
  · intro t
    exact
      simpleRandomWalk_hlozExceptional_series_ne_top_of_balance_rank_source_series
        hmax product t (hbalance t) (hsourceOne t) (hsourceTwo t)
          (hsourceThree t) (hcomplement t)
  · exact hsubset₁
  · exact hsubset₂
  · exact hsubset₃
  · exact hmajor₁
  · exact hmajor₂
  · exact hmajor₃

end

end Erdos1165.HLOZNoLazyInitialBudgetUpperAssembly
