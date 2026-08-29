/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGlobalLocalReferenceClassification

/-!
# Global edge summary of classified local contacts

This module performs only the truthful casewise edge aggregation.  A finite
exception-free contact contributes its global imaginary shortcut.  A
reference-covered finite or infinite contact contributes the real forward
edges of its literal alternating witness.  No warp, source-cover, or splice
compatibility conclusion is asserted here.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry
namespace LimitingClosedEndpointPairing

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Zf : FracturedWarp Gamma}
variable {X before innerRoof outerRoof persistent : Set V}

/-- A fixed witness for one finite endpoint pair. -/
noncomputable def finiteChoice
    (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent)
    (s) (v : V) (hsv : A.endpoint s = some v) :
    LimitingFiniteEndpointWitness C Zf X before innerRoof outerRoof s.1 v :=
  (A.finite_witness s v hsv).some

/-- A fixed witness for one infinite endpoint outcome. -/
noncomputable def infiniteChoice
    (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent)
    (s) (hs : A.endpoint s = none) :
    LimitingInfiniteEndpointWitness C Zf X before innerRoof outerRoof
      persistent s.1 :=
  (A.infinite_witness s hs).some

/-- Edges retained from all finite classified occurrences. -/
def finiteRetainedEdges
  (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent) : Set (V × V) :=
  {e | ∃ s v, ∃ hsv : A.endpoint s = some v,
    e ∈ (A.finiteChoice s v hsv).classification.retainedEdges}

/-- Global imaginary shortcuts contributed by exception-free finite
occurrences. -/
def shortcutEdges
  (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent) : Set (V × V) :=
  {e | ∃ s v, ∃ hsv : A.endpoint s = some v,
    e ∈ (A.finiteChoice s v hsv).classification.shortcutEdges}

/-- Real forward edges contributed by reference-covered finite
occurrences. -/
def finiteCoveredForwardEdges
  (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent) : Set (V × V) :=
  {e | ∃ s v, ∃ hsv : A.endpoint s = some v,
    e ∈ (A.finiteChoice s v hsv).classification.retainedEdges \
      (A.finiteChoice s v hsv).classification.shortcutEdges}

/-- Real forward edges retained from the covered infinite occurrences;
popular occurrences contribute the empty set. -/
def infiniteCoveredForwardEdges
  (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent) : Set (V × V) :=
  {e | ∃ s, ∃ hs : A.endpoint s = none,
    e ∈ (A.infiniteChoice s hs).classification.retainedEdges}

/-- All real forward edges retained from covered occurrences. -/
def coveredForwardEdges
    (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent) : Set (V × V) :=
  A.finiteCoveredForwardEdges ∪ A.infiniteCoveredForwardEdges

/-- The complete truthful contact-edge contribution. -/
def retainedEdges
    (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent) : Set (V × V) :=
  A.finiteRetainedEdges ∪ A.infiniteCoveredForwardEdges

private theorem directionEdges_subset_edgeSet
    (Q : AltPath Gamma.graph) (d : Direction) :
    Q.directionEdges d ⊆ Q.edgeSet := by
  intro e he
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, _hd, hel⟩ := he
  rw [Q.edgeSet_eq_iUnion_links]
  simp only [Set.mem_iUnion]
  exact ⟨l, hl, hel⟩

private theorem finiteCovered_subset_realGraph
    {Q : AltPath Gamma.graph} {u v : V}
    (K : LimitingFiniteContactClassification C X Q u v) :
    K.retainedEdges \ K.shortcutEdges ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  cases K with
  | imaginary h => simp [LimitingFiniteContactClassification.retainedEdges,
      LimitingFiniteContactClassification.shortcutEdges]
  | initialCovered h =>
      intro e he
      exact Q.edgeSet_subset_adj
        (directionEdges_subset_edgeSet Q .forward he.1)
  | terminalCovered h =>
      intro e he
      exact Q.edgeSet_subset_adj
        (directionEdges_subset_edgeSet Q .forward he.1)

private theorem finiteShortcut_subset_retained
    {Q : AltPath Gamma.graph} {u v : V}
    (K : LimitingFiniteContactClassification C X Q u v) :
    K.shortcutEdges ⊆ K.retainedEdges := by
  cases K <;> simp [LimitingFiniteContactClassification.retainedEdges,
    LimitingFiniteContactClassification.shortcutEdges]

private theorem infiniteRetained_subset_realGraph
    {Q : AltPath Gamma.graph} {u : V}
    (K : LimitingInfiniteContactClassification C X persistent Q u) :
    K.retainedEdges ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  cases K with
  | popular h => simp [LimitingInfiniteContactClassification.retainedEdges]
  | initialCovered h =>
      intro e he
      exact Q.edgeSet_subset_adj
        (directionEdges_subset_edgeSet Q .forward he)

/-- The contact contribution splits exactly into global shortcuts and
covered real forward edges. -/
theorem retainedEdges_eq_shortcut_union_coveredForward
    (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent) :
    A.retainedEdges = A.shortcutEdges ∪ A.coveredForwardEdges := by
  ext e
  constructor
  · rintro (⟨s, v, hsv, he⟩ | he)
    · by_cases hs : e ∈
          (A.finiteChoice s v hsv).classification.shortcutEdges
      · exact Or.inl ⟨s, v, hsv, hs⟩
      · exact Or.inr (Or.inl ⟨s, v, hsv, he, hs⟩)
    · exact Or.inr (Or.inr he)
  · rintro (he | he)
    · obtain ⟨s, v, hsv, he⟩ := he
      left
      exact ⟨s, v, hsv, finiteShortcut_subset_retained
        (A.finiteChoice s v hsv).classification he⟩
    · rcases he with he | he
      · obtain ⟨s, v, hsv, he, _⟩ := he
        exact Or.inl ⟨s, v, hsv, he⟩
      · exact Or.inr he

/-- Every shortcut is a genuine edge of the limiting-reference imaginary
graph. -/
theorem shortcutEdges_subset_imaginaryGraph
    (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent) :
    A.shortcutEdges ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  rintro e ⟨s, v, hsv, he⟩
  exact (A.finiteChoice s v hsv).classification
    |>.shortcutEdges_subset_imaginaryGraph he

/-- Covered occurrences contribute only literal original-web forward
edges. -/
theorem coveredForwardEdges_subset_realGraph
    (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent) :
    A.coveredForwardEdges ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  rintro e (he | he)
  · obtain ⟨s, v, hsv, he⟩ := he
    exact finiteCovered_subset_realGraph
      (A.finiteChoice s v hsv).classification he
  · obtain ⟨s, hs, he⟩ := he
    exact infiniteRetained_subset_realGraph
      (A.infiniteChoice s hs).classification he

/-- Consequently the complete casewise contribution is honest in the
global imaginary graph. -/
theorem retainedEdges_subset_imaginaryGraph
    (A : LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent) :
    A.retainedEdges ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  rw [A.retainedEdges_eq_shortcut_union_coveredForward]
  rintro e (he | he)
  · exact A.shortcutEdges_subset_imaginaryGraph he
  · exact Or.inl (A.coveredForwardEdges_subset_realGraph he)

end LimitingClosedEndpointPairing
end ClubStageGeometry
end Erdos599.Blueprint.LinkageBlueprint
