/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZNoLazyHeterogeneousTransitionFactors

/-!
# Direct-series endgame for the no-lazy filtered chain

This intermediate adapter is the common analytic seam for the two honest
low-gap closures: one may first construct `HasGapDeficitReturnHarnack` and
derive the HLOZ exceptional series, or prove that series directly.  The
eventual public assembly constructs the series from literal data before
calling this theorem; it does not expose the series as a final premise.

The paid side is likewise accepted either as the already assembled finite
mesh series or as three rankwise majorants.  No lazy event occurs in either
form.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZNoLazyDirectSeriesEndgame

open HLOZFilteredTransitionAssembly HLOZNoLazyFilteredTransitions
open HLOZNoLazyHeterogeneousTransitionFactors HLOZPathEvents
open HLOZPositiveLevelFilteredTransitionAssembly

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

set_option linter.constructorNameAsVariable false in
/-- Internal no-lazy endgame from the two already derived summable series.

Neither series is intended to be a premise of the final upper theorem: the
literal Raw/Theta package constructs them and then invokes this adapter. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_noLazy_factors_and_direct_series
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0)
    (factors : ∀ t : DominoTiling,
      PositiveLevelNoLazyHeterogeneousTransitionFactorPackage
        properGapMesh stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t)
    (hbase : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (hpaid : ∀ t, ∑' m, simpleRandomWalk
      (UpperAssembly.meshBranchUnion properGapMesh
        (candidatePaidBadHistoryEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m)) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  let start : DominoTiling → ℕ := fun t ↦ (factors t).levelStart
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_positiveLevel_filtered_estimates
      start K
      (firstFactorBadHistory stagedCandidate₁)
      (secondFactorBadHistory stagedCandidate₂)
      (thirdFactorBadHistory stagedCandidate₃)
      (candidatePaidBadHistoryEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃)
      (noLazy_terminalFilteredBadHistoryRouting stagedCandidate₁
        stagedCandidate₂ stagedCandidate₃)
  · intro t m a hm
    have hm' : (factors t).levelStart ≤ m := by
      simpa only [start] using hm
    rw [tailGoodFirstTransitionEvent, if_pos hm]
    exact (factors t).first_measure_estimate m hm' a
  · intro t m a hm
    have hm' : (factors t).levelStart ≤ m := by
      simpa only [start] using hm
    rw [tailGoodSecondTransitionEvent, if_pos hm,
      tailGoodFirstTransitionEvent, if_pos hm]
    exact (factors t).second_measure_estimate m hm' a
  · intro t m a hm
    have hm' : (factors t).levelStart ≤ m := by
      simpa only [start] using hm
    rw [tailGoodThirdTransitionEvent, if_pos hm,
      tailGoodSecondTransitionEvent, if_pos hm]
    exact (factors t).third_measure_estimate m hm' a
  · exact hbase
  · exact hpaid

set_option linter.constructorNameAsVariable false in
/-- Direct-series endgame in the exact rank-majorant form exported by the
raw source/Theta decomposition. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_noLazy_factors_and_rank_majorants
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0)
    (factors : ∀ t : DominoTiling,
      PositiveLevelNoLazyHeterogeneousTransitionFactorPackage
        properGapMesh stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t)
    (hbase : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (major₁ major₂ major₃ : DominoTiling → ℕ → Set WalkPath)
    (hsubset₁ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        stagedCandidate₁ t m a ⊆ major₁ t m)
    (hsubset₂ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        stagedCandidate₂ t m a ⊆ major₂ t m)
    (hsubset₃ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        stagedCandidate₃ t m a ⊆ major₃ t m)
    (hmajor₁ : ∀ t, ∑' m, simpleRandomWalk (major₁ t m) ≠ ∞)
    (hmajor₂ : ∀ t, ∑' m, simpleRandomWalk (major₂ t m) ≠ ∞)
    (hmajor₃ : ∀ t, ∑' m, simpleRandomWalk (major₃ t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_noLazy_factors_and_direct_series
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K factors hbase
  intro t
  exact candidatePaidBadHistoryEvent_series_ne_top_of_rank_majorants
    properGapMesh stagedCandidate₁ stagedCandidate₂ stagedCandidate₃
    major₁ major₂ major₃ t (hsubset₁ t) (hsubset₂ t) (hsubset₃ t)
    (hmajor₁ t) (hmajor₂ t) (hmajor₃ t)

end

end Erdos1165.HLOZNoLazyDirectSeriesEndgame
