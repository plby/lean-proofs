/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFilteredTransitionAssembly

/-!
# Positive-level source-correct transition assembly

The stopped-history product laws and the strong-Markov factors used in the
HLOZ upper bound are eventual statements.  This module absorbs the finitely
many earlier favorite levels into the exceptional family.  It therefore
never asks a concrete transition constructor to manufacture a certificate
at level zero or below its deterministic law threshold.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZPositiveLevelFilteredTransitionAssembly

open HLOZFilteredTransitionAssembly HLOZPathEvents

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := (GapScale × GapScale) × GapScale
abbrev BranchEvent := DominoTiling → ℕ → GapTriple → Set WalkPath

/-- The first filtered transition on the certified tail, and the empty event
before the certificate threshold. -/
def tailGoodFirstTransitionEvent (start : DominoTiling → ℕ)
    (bad₁ : BranchEvent) : BranchEvent := fun t m a ↦
  if start t ≤ m then goodFirstTransitionEvent bad₁ t m a else ∅

/-- The second filtered transition on the certified tail. -/
def tailGoodSecondTransitionEvent (start : DominoTiling → ℕ)
    (bad₁ bad₂ : BranchEvent) : BranchEvent := fun t m a ↦
  if start t ≤ m then goodSecondTransitionEvent bad₁ bad₂ t m a else ∅

/-- The third filtered transition on the certified tail. -/
def tailGoodThirdTransitionEvent (start : DominoTiling → ℕ)
    (bad₁ bad₂ bad₃ : BranchEvent) : BranchEvent := fun t m a ↦
  if start t ≤ m then
    goodThirdTransitionEvent bad₁ bad₂ bad₃ t m a
  else ∅

/-- The source-correct exceptional family together with the finite prefix of
separated-level events before the transition certificates start. -/
def positiveLevelSourceCorrectExceptionalEvent
    (start : DominoTiling → ℕ) (paid : BranchEvent)
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  sourceCorrectFilteredExceptionalEvent paid t m ∪
    if m < start t then hlozSeparatedLevelEvent t m else ∅

/-- The source-correct mesh cover remains valid after tail truncation. -/
theorem positiveLevel_sourceCorrect_filtered_mesh_cover
    (start : DominoTiling → ℕ) (bad₁ bad₂ bad₃ paid : BranchEvent)
    (route : TerminalFilteredBadHistoryRouting bad₁ bad₂ bad₃ paid)
    (t : DominoTiling) (m : ℕ) :
    hlozSeparatedLevelEvent t m ⊆
      positiveLevelSourceCorrectExceptionalEvent start paid t m ∪
        UpperAssembly.meshBranchUnion properGapMesh
          (tailGoodThirdTransitionEvent start bad₁ bad₂ bad₃ t m) := by
  by_cases hm : start t ≤ m
  · have hnot : ¬m < start t := Nat.not_lt_of_ge hm
    have htail : tailGoodThirdTransitionEvent start bad₁ bad₂ bad₃ t m =
        goodThirdTransitionEvent bad₁ bad₂ bad₃ t m := by
      funext a
      rw [tailGoodThirdTransitionEvent, if_pos hm]
    rw [positiveLevelSourceCorrectExceptionalEvent, if_neg hnot,
      union_empty, htail]
    exact hlozSeparatedLevelEvent_sourceCorrect_filtered_mesh_cover
      bad₁ bad₂ bad₃ paid route t m
  · have hlt : m < start t := Nat.lt_of_not_ge hm
    intro s hs
    exact Or.inl (Or.inr (by simpa [hlt] using hs))

/-- Adding the finite uncertified prefix preserves exceptional summability. -/
theorem positiveLevelSourceCorrectExceptional_series_ne_top
    (start : DominoTiling → ℕ) (paid : BranchEvent) (t : DominoTiling)
    (hbase : ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (hpaid : ∑' m,
      simpleRandomWalk (paidTransitionBadHistoryEvent paid t m) ≠ ∞) :
    ∑' m, simpleRandomWalk
      (positiveLevelSourceCorrectExceptionalEvent start paid t m) ≠ ∞ := by
  let small : ℕ → ℝ≥0∞ := fun m ↦
    if m < start t then simpleRandomWalk (hlozSeparatedLevelEvent t m) else 0
  have hsmall : ∑' m, small m ≠ ∞ := by
    rw [tsum_eq_sum (s := Finset.range (start t))]
    · apply ENNReal.sum_ne_top.mpr
      intro m hm
      have hlt : m < start t := Finset.mem_range.mp hm
      simp only [small, if_pos hlt]
      exact measure_ne_top _ _
    · intro m hm
      have hnot : ¬m < start t := by
        simpa [Finset.mem_range] using hm
      simp [small, hnot]
  have hsource := sourceCorrectFilteredExceptional_series_ne_top paid t
    hbase hpaid
  have hpoint : ∀ m,
      simpleRandomWalk
          (positiveLevelSourceCorrectExceptionalEvent start paid t m) ≤
        simpleRandomWalk (sourceCorrectFilteredExceptionalEvent paid t m) +
          small m := by
    intro m
    refine (measure_union_le _ _).trans ?_
    change simpleRandomWalk (sourceCorrectFilteredExceptionalEvent paid t m) +
        simpleRandomWalk
          (if m < start t then hlozSeparatedLevelEvent t m else ∅) ≤ _
    by_cases hm : m < start t <;> simp [small, hm]
  have hmajor : ∑' m,
      (simpleRandomWalk (sourceCorrectFilteredExceptionalEvent paid t m) +
        small m) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hsource, hsmall⟩
  exact ne_top_of_le_ne_top hmajor (ENNReal.tsum_le_tsum hpoint)

set_option linter.constructorNameAsVariable false in
/-- Internal positive-level endgame for filtered estimates.  Concrete upper
assemblies should derive the three tail estimates from stopped-history and
future-factor certificates before invoking this theorem. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_positiveLevel_filtered_estimates
    (start : DominoTiling → ℕ) (K : ℝ≥0)
    (bad₁ bad₂ bad₃ paid : BranchEvent)
    (route : TerminalFilteredBadHistoryRouting bad₁ bad₂ bad₃ paid)
    (hfirst : ∀ t m a, start t ≤ m →
      a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk
          (tailGoodFirstTransitionEvent start bad₁ t m a) ≤
        UpperCanonical.hlozTransitionCost K m)
    (hsecond : ∀ t m a, start t ≤ m →
      a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk
          (tailGoodSecondTransitionEvent start bad₁ bad₂ t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk
            (tailGoodFirstTransitionEvent start bad₁ t m a))
    (hthird : ∀ t m a, start t ≤ m →
      a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk
          (tailGoodThirdTransitionEvent start bad₁ bad₂ bad₃ t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk
            (tailGoodSecondTransitionEvent start bad₁ bad₂ t m a))
    (hbase : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (hpaid : ∀ t, ∑' m,
      simpleRandomWalk (paidTransitionBadHistoryEvent paid t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  have hscreened : ∀ t,
      ∑' m, simpleRandomWalk (hlozSeparatedLevelEvent t m) ≠ ∞ := by
    intro t
    apply UpperAssembly.screenedLevel_series_ne_top simpleRandomWalk properGapMesh
      (hlozSeparatedLevelEvent t)
      (positiveLevelSourceCorrectExceptionalEvent start paid t)
      (tailGoodFirstTransitionEvent start bad₁ t)
      (tailGoodSecondTransitionEvent start bad₁ bad₂ t)
      (tailGoodThirdTransitionEvent start bad₁ bad₂ bad₃ t)
      (UpperCanonical.hlozTransitionCost K) (K ^ 3)
      (3 * ScreeningInstantiation.kappa)
    · exact ScreeningInstantiation.hloz_parameter_inequalities.2.2.2.2.2.2.2.1
    · exact positiveLevel_sourceCorrect_filtered_mesh_cover
        start bad₁ bad₂ bad₃ paid route t
    · intro m
      by_cases hm : start t ≤ m
      · intro a
        exact hfirst t m a hm
      · intro a _ha
        rw [tailGoodFirstTransitionEvent, if_neg hm, measure_empty]
        exact bot_le
    · intro m
      by_cases hm : start t ≤ m
      · intro a
        exact hsecond t m a hm
      · intro a _ha
        rw [tailGoodSecondTransitionEvent, if_neg hm, measure_empty]
        exact bot_le
    · intro m
      by_cases hm : start t ≤ m
      · intro a
        exact hthird t m a hm
      · intro a _ha
        rw [tailGoodThirdTransitionEvent, if_neg hm, measure_empty]
        exact bot_le
    · exact positiveLevelSourceCorrectExceptional_series_ne_top
        start paid t (hbase t) (hpaid t)
    · intro m
      exact (UpperCanonical.hlozTransitionCost_cube K m).le
  have hsum : ∑' m, simpleRandomWalk (levelFavoriteSet m 4) ≠ ∞ :=
    level_event_summable_of_six_tilings simpleRandomWalk
      levelFavoriteSet_four_subset_six_hloz_tilings hscreened
  exact UpperAssembly.ae_eventually_favoriteCount_le_three_of_M4_summable
    simpleRandomWalk hsum simpleRandomWalk_maxLocalTime_tendsto

end

end Erdos1165.HLOZPositiveLevelFilteredTransitionAssembly
