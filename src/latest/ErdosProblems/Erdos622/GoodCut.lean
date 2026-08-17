/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import ErdosProblems.Erdos622.LinearForest

/-!
# Linear forests and good cuts for Erdős Problem 622

This file formalizes the deterministic definitions used in the almost-bipartite part of
Draganić--Keevash--Müyesser's proof.  All graphs below are finite simple graphs.

The shared `LinearForest` module supplies the faithful finite linear-forest predicate, exact edge
truncation, and the predicate saying that an induced part contains a sufficiently large linear
forest.  This file builds the symmetric `k`-good-cut interface used by the almost-bipartite branch.
-/

open scoped SimpleGraph

namespace Erdos622

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ContainsLinearForestWith

variable {G : SimpleGraph V} {X : Finset V} {r : ℕ}

/-- A supported matching, in the degree-at-most-one formulation, is an internal linear-forest
witness. -/
theorem of_degree_le_one {F : SimpleGraph V} (hFG : F ≤ G)
    (hdegree : ∀ v, F.degree v ≤ 1) (hsupp : F.support ⊆ (X : Set V))
    (hcard : r ≤ F.edgeFinset.card) : ContainsLinearForestWith G X r :=
  ⟨F, hFG, (MatchingGraph.of_degree_le_one hdegree).linearForest, hsupp, hcard⟩

end ContainsLinearForestWith

/-- `X` and `Y` form a cut (a disjoint partition of the finite vertex set). -/
def IsCut (X Y : Finset V) : Prop :=
  Disjoint X Y ∧ X ∪ Y = Finset.univ

namespace IsCut

variable {X Y : Finset V}

/-- Swapping the two sides preserves being a cut. -/
theorem symm (h : IsCut X Y) : IsCut Y X := by
  exact ⟨h.1.symm, by simpa [Finset.union_comm] using h.2⟩

/-- Membership in the right side is the complement of membership in the left side. -/
theorem mem_right_iff (h : IsCut X Y) (v : V) : v ∈ Y ↔ v ∉ X := by
  constructor
  · intro hvY hvX
    exact Finset.disjoint_left.mp h.1 hvX hvY
  · intro hvX
    have hvUnion : v ∈ X ∪ Y := by simpa [h.2]
    simpa [hvX] using hvUnion

/-- Membership in the left side is the complement of membership in the right side. -/
theorem mem_left_iff (h : IsCut X Y) (v : V) : v ∈ X ↔ v ∉ Y := by
  simpa using h.symm.mem_right_iff v

/-- The cardinalities of the two sides add to the number of vertices. -/
theorem card_add_card (h : IsCut X Y) : X.card + Y.card = Fintype.card V := by
  rw [← Finset.card_union_of_disjoint h.1, h.2, Finset.card_univ]

/-- On an oriented cut, the larger side is the smaller side plus the imbalance. -/
theorem card_eq_card_add_sub (hcard : Y.card ≤ X.card) :
    X.card = Y.card + (X.card - Y.card) := by
  omega

end IsCut

/-- The DKM definition of a `k`-good cut.

The larger side must contain a linear forest whose number of edges is at least the imbalance plus
`k`.  The disjunction makes the definition invariant under swapping the sides.
-/
def IsKGoodCut (G : SimpleGraph V) (X Y : Finset V) (k : ℕ) : Prop :=
  IsCut X Y ∧
    ((Y.card ≤ X.card ∧
        ContainsLinearForestWith G X (k + (X.card - Y.card))) ∨
      (X.card ≤ Y.card ∧
        ContainsLinearForestWith G Y (k + (Y.card - X.card))))

/-- A good cut is a `0`-good cut. -/
abbrev IsGoodCut (G : SimpleGraph V) (X Y : Finset V) : Prop :=
  IsKGoodCut G X Y 0

namespace IsKGoodCut

variable {G G' : SimpleGraph V} {X Y : Finset V} {j k : ℕ}

/-- The definition of a good cut is symmetric in its two sides. -/
theorem symm (h : IsKGoodCut G X Y k) : IsKGoodCut G Y X k := by
  refine ⟨h.1.symm, ?_⟩
  exact h.2.elim Or.inr Or.inl

/-- A `k`-good cut is `j`-good for every `j ≤ k`. -/
theorem mono (h : IsKGoodCut G X Y k) (hjk : j ≤ k) : IsKGoodCut G X Y j := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hX | hY
  · left
    refine ⟨hX.1, hX.2.mono_requirement ?_⟩
    exact Nat.add_le_add_right hjk _
  · right
    refine ⟨hY.1, hY.2.mono_requirement ?_⟩
    exact Nat.add_le_add_right hjk _

/-- Every `k`-good cut is good. -/
theorem good (h : IsKGoodCut G X Y k) : IsGoodCut G X Y :=
  h.mono (Nat.zero_le k)

/-- Enlarging the graph preserves a fixed good-cut witness. -/
theorem mono_graph (h : IsKGoodCut G X Y k) (hGG' : G ≤ G') :
    IsKGoodCut G' X Y k := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hX | hY
  · exact Or.inl ⟨hX.1, hX.2.mono_graph hGG'⟩
  · exact Or.inr ⟨hY.1, hY.2.mono_graph hGG'⟩

/-- On the orientation `|Y| ≤ |X|`, a `k`-good witness in `X` can be truncated to exactly the
required number of edges. -/
theorem exists_exact_left (_hcut : IsCut X Y) (_hcard : Y.card ≤ X.card)
    (hforest : ContainsLinearForestWith G X (k + (X.card - Y.card))) :
    ∃ F : SimpleGraph V,
      F ≤ G ∧ LinearForest F ∧ F.support ⊆ (X : Set V) ∧
        F.edgeFinset.card = k + (X.card - Y.card) := by
  exact hforest.exists_exact

/-- A `k`-good cut comes with an exact forest on one of its larger sides. -/
theorem exists_exact (h : IsKGoodCut G X Y k) :
    (∃ F : SimpleGraph V,
      Y.card ≤ X.card ∧ F ≤ G ∧ LinearForest F ∧ F.support ⊆ (X : Set V) ∧
        F.edgeFinset.card = k + (X.card - Y.card)) ∨
    (∃ F : SimpleGraph V,
      X.card ≤ Y.card ∧ F ≤ G ∧ LinearForest F ∧ F.support ⊆ (Y : Set V) ∧
        F.edgeFinset.card = k + (Y.card - X.card)) := by
  rcases h.2 with hX | hY
  · left
    obtain ⟨F, hFG, hlin, hsupp, hcard⟩ := hX.2.exists_exact
    exact ⟨F, hX.1, hFG, hlin, hsupp, hcard⟩
  · right
    obtain ⟨F, hFG, hlin, hsupp, hcard⟩ := hY.2.exists_exact
    exact ⟨F, hY.1, hFG, hlin, hsupp, hcard⟩

end IsKGoodCut

end Erdos622
