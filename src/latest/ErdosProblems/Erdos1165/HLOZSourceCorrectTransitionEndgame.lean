/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFilteredTransitionAssembly
import ErdosProblems.Erdos1165.HLOZStoppedHistoryCandidateFuture

/-!
# Source-correct Proposition 4.7 endgame

This module feeds the future-factor certificates matching HLOZ
(4.36)--(4.37) into the additive filtered-history assembly.  Consequently
the public theorem below has no hypothesis asserting any of the three
transition probability inequalities.  They are derived branch by branch
from stopped-history coordinate ratios, pathwise future containments, and
full-tail strong Markov.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZSourceCorrectTransitionEndgame

open HLOZPathEvents HLOZFilteredTransitionAssembly
open HLOZStoppedHistoryCandidateFuture

noncomputable section

abbrev DominoTiling := HLOZFilteredTransitionAssembly.DominoTiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-- Measurability of cumulatively filtered stages from measurability of the
rank-local stopped-history filters. -/
theorem measurableSet_goodFirstTransitionEvent
    (bad₁ : BranchEvent)
    (hbad₁ : ∀ t m a, MeasurableSet (bad₁ t m a))
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (goodFirstTransitionEvent bad₁ t m a) :=
  (HLOZPathEvents.measurableSet_firstTransitionEvent t m a).diff
    (hbad₁ t m a)

theorem measurableSet_goodSecondTransitionEvent
    (bad₁ bad₂ : BranchEvent)
    (hbad₁ : ∀ t m a, MeasurableSet (bad₁ t m a))
    (hbad₂ : ∀ t m a, MeasurableSet (bad₂ t m a))
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (goodSecondTransitionEvent bad₁ bad₂ t m a) :=
  (HLOZPathEvents.measurableSet_secondTransitionEvent t m a).diff
    ((hbad₁ t m a).union (hbad₂ t m a))

theorem measurableSet_goodThirdTransitionEvent
    (bad₁ bad₂ bad₃ : BranchEvent)
    (hbad₁ : ∀ t m a, MeasurableSet (bad₁ t m a))
    (hbad₂ : ∀ t m a, MeasurableSet (bad₂ t m a))
    (hbad₃ : ∀ t m a, MeasurableSet (bad₃ t m a))
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet
      (goodThirdTransitionEvent bad₁ bad₂ bad₃ t m a) :=
  (HLOZPathEvents.measurableSet_screenedThirdTransitionEvent t m a).diff
    (((hbad₁ t m a).union (hbad₂ t m a)).union (hbad₃ t m a))

set_option linter.constructorNameAsVariable false in
/-- Public source-correct upper theorem over an explicit family of
stopped-history/future certificates.

The hypotheses concern only:

* measurable rank-local stopped-history filters;
* a high- or low-scale source certificate on each finite mesh branch;
* summability of the original exceptional family and of the additively paid
  bad-history family.

In particular there is no `hfirst`, `hsecond`, or `hthird` probability
hypothesis. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_sourceCorrectFactors
    (K : ℝ≥0) (bad₁ bad₂ bad₃ paid : BranchEvent)
    (route : TerminalFilteredBadHistoryRouting bad₁ bad₂ bad₃ paid)
    (hbad₁ : ∀ t m a, MeasurableSet (bad₁ t m a))
    (hbad₂ : ∀ t m a, MeasurableSet (bad₂ t m a))
    (hbad₃ : ∀ t m a, MeasurableSet (bad₃ t m a))
    {History Candidate State : Type*}
    [Countable History] [Countable State]
    (firstFactors : ∀ t m (a : GapTriple),
      SourceCorrectTransitionFactor History Candidate State Set.univ
        (goodFirstTransitionEvent bad₁ t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (secondFactors : ∀ t m (a : GapTriple),
      SourceCorrectTransitionFactor History Candidate State
        (goodFirstTransitionEvent bad₁ t m a)
        (goodSecondTransitionEvent bad₁ bad₂ t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (thirdFactors : ∀ t m (a : GapTriple),
      SourceCorrectTransitionFactor History Candidate State
        (goodSecondTransitionEvent bad₁ bad₂ t m a)
        (goodThirdTransitionEvent bad₁ bad₂ bad₃ t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (hbase : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (hpaid : ∀ t, ∑' m,
      simpleRandomWalk
        (paidTransitionBadHistoryEvent paid t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_sourceCorrect_filtered_estimates
      K bad₁ bad₂ bad₃ paid route
  · intro t m a ha
    clear ha
    have hfirstMeas : MeasurableSet
        (goodFirstTransitionEvent bad₁ t m a) :=
      measurableSet_goodFirstTransitionEvent bad₁ hbad₁ t m a
    have h := @SourceCorrectTransitionFactor.measure_next_le
      History Candidate State _ _ Set.univ
      (goodFirstTransitionEvent bad₁ t m a)
      (UpperCanonical.hlozTransitionCost K m)
      (firstFactors t m a)
      MeasurableSet.univ hfirstMeas
    simpa using h
  · intro t m a ha
    clear ha
    have hfirstMeas : MeasurableSet
        (goodFirstTransitionEvent bad₁ t m a) :=
      measurableSet_goodFirstTransitionEvent bad₁ hbad₁ t m a
    have hsecondMeas : MeasurableSet
        (goodSecondTransitionEvent bad₁ bad₂ t m a) :=
      measurableSet_goodSecondTransitionEvent bad₁ bad₂
        hbad₁ hbad₂ t m a
    exact @SourceCorrectTransitionFactor.measure_next_le
      History Candidate State _ _
      (goodFirstTransitionEvent bad₁ t m a)
      (goodSecondTransitionEvent bad₁ bad₂ t m a)
      (UpperCanonical.hlozTransitionCost K m)
      (secondFactors t m a) hfirstMeas hsecondMeas
  · intro t m a ha
    clear ha
    have hsecondMeas : MeasurableSet
        (goodSecondTransitionEvent bad₁ bad₂ t m a) :=
      measurableSet_goodSecondTransitionEvent bad₁ bad₂
        hbad₁ hbad₂ t m a
    have hthirdMeas : MeasurableSet
        (goodThirdTransitionEvent bad₁ bad₂ bad₃ t m a) :=
      measurableSet_goodThirdTransitionEvent bad₁ bad₂ bad₃
        hbad₁ hbad₂ hbad₃ t m a
    exact @SourceCorrectTransitionFactor.measure_next_le
      History Candidate State _ _
      (goodSecondTransitionEvent bad₁ bad₂ t m a)
      (goodThirdTransitionEvent bad₁ bad₂ bad₃ t m a)
      (UpperCanonical.hlozTransitionCost K m)
      (thirdFactors t m a) hsecondMeas hthirdMeas
  · exact hbase
  · exact hpaid

end

end Erdos1165.HLOZSourceCorrectTransitionEndgame
