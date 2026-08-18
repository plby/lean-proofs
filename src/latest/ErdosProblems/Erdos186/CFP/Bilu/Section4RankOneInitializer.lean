/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section91PresentationCubification
import ErdosProblems.Erdos186.CFP.Bilu.Section4TerminalScaledRealization

/-!
# A total rank-one initializer for integer sets

The Section 4 candidate class needs an initial presentation even outside
the small-doubling branch.  Since the target group is `ℤ`, evaluation in
one coordinate already maps onto every source element; cubification then
rescales the norm to contain the finitely many required lifts.
-/

namespace Erdos186.CFP.Bilu.Section4RankOneInitializer

open Mahler
open Section90IntegerInitialization
open Section91IntegerPresentation
open Section91PresentationCubification
open Section92PresentationDescent
open Section4TerminalScaledRealization

noncomputable section

set_option autoImplicit false

/-- Literal rank-one lifts through coordinate evaluation. -/
theorem exists_singletonValue_lift (A : Finset ℤ) (a : ℤ) (_ha : a ∈ A) :
    ∃ z : IntegralPoint 1, singletonValue z = a := by
  exact ⟨singletonPoint a, singletonValue_singletonPoint a⟩

/-- Every finite integer set has a positive-volume rank-one body
presentation.  Its radius may depend on the set, while its rank does not. -/
def rankOneBodyPresentation (A : Finset ℤ) : BodyPresentation A 1 :=
  cubifiedBodyPresentation zero_lt_one singletonValue
    (exists_singletonValue_lift A)

/-- Bundled rank-one presentation. -/
def rankedRankOneBodyPresentation (A : Finset ℤ) :
    RankedBodyPresentation A :=
  ⟨1, rankOneBodyPresentation A⟩

@[simp] theorem rank_rankedRankOneBodyPresentation (A : Finset ℤ) :
    (rankedRankOneBodyPresentation A).1 = 1 := rfl

/-- Rank-bounded form used as the total large-cardinality initializer. -/
def rankBoundedRankOneBodyPresentation
    (rankBound : ℕ) (hrankBound : 1 ≤ rankBound) (A : Finset ℤ) :
    RankBoundedBodyPresentation A rankBound :=
  ⟨rankedRankOneBodyPresentation A, hrankBound⟩

end


end Erdos186.CFP.Bilu.Section4RankOneInitializer

#print axioms
  Erdos186.CFP.Bilu.Section4RankOneInitializer.rankOneBodyPresentation
