/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailablePairDegree

/-! # Pair-local two-away cutoffs -/

namespace Erdos207

open Finset

/-- Two-away targets which are not already pair-sharing deletions. -/
def nonPairTwoAwayForbiddenTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : TripleSystemOn V) (U : TripleOn V) :
    TripleSystemOn V :=
  twoAwayForbiddenTriangles F S U \ triplesSharingPair U

/-- Local genuinely two-away cutoff inside every currently available pair
star.  Pair-sharing targets are charged to the separate three-vertex term.
The selector is required not to cover the tracked pair, exactly as in a
surviving pair-star transition. -/
def HasPairTwoAwayCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (S : GreedyStateOn V) : Prop :=
  ∀ U ∈ S.available, ∀ P : Finset V, P.card = 2 → ¬ P ⊆ U.1 →
    (availableTrianglesContainingPair S P ∩
      nonPairTwoAwayForbiddenTriangles F S.chosen U).card ≤ K

/-- A global cutoff implies the corresponding local cutoff with the same
threshold. -/
theorem HasTwoAwayCutoff.hasPairTwoAwayCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {K : ℕ} {S : GreedyStateOn V}
    (h : HasTwoAwayCutoff F K S) : HasPairTwoAwayCutoff F K S := by
  intro U hU P _hP _hPU
  exact (card_le_card (inter_subset_right.trans sdiff_subset)).trans (h U hU)

end Erdos207
