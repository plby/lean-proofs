/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeLinkingPath

/-!
# Restricting native occurrences to untouched reference subwarps

If all actually removed reference edges lie in a literal subwarp, a safe
word restricts to that subwarp. Avoidance of the discarded owners supplies
this edge hypothesis. The switched relation only shrinks, so finite
nondegeneracy survives. No finite-character assumption is needed here.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y Local : Set Gamma.DPath}

private theorem subwarp_edges_subset (hsub : Local ⊆ Y) :
    familyEdges Local ⊆ familyEdges Y := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, he⟩ := he
  exact ⟨p, hsub hp, he⟩

namespace Alternating.FiniteColouredOccurrenceWord

def restrictReference (Q : FiniteColouredOccurrenceWord W Y)
    (hback : Q.backwardEdges ⊆ familyEdges Local) :
    FiniteColouredOccurrenceWord W Local where
  length := Q.length
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hd : Q.direction i with
    | forward => simpa only [hd] using Q.actualEdge_spec i
    | backward =>
        apply hback
        refine ⟨⟨i, by simp [hd]⟩, ?_⟩
        simp [backwardEdge, actualEdge, hd]
  occurrence_injective := Q.occurrence_injective

theorem IsIntervalSafe.restrictReference
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hsub : Local ⊆ Y) (hback : Q.backwardEdges ⊆ familyEdges Local) :
    (Q.restrictReference hback).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    exact hQ.incoming_removed hxy (subwarp_edges_subset hsub hby)
  · intro x y b hxy hxb
    exact hQ.outgoing_removed hxy (subwarp_edges_subset hsub hxb)
  · intro p hp
    exact hQ.intervals p (hsub hp)
  · intro x y hxy
    refine ⟨?_, ?_⟩
    · rintro ⟨p, hp, hpy⟩
      exact (hQ.endpoint_pure hxy).1 ⟨p, hsub hp, hpy⟩
    · rintro ⟨p, hp, hpx⟩
      exact (hQ.endpoint_pure hxy).2 ⟨p, hsub hp, hpx⟩

end Alternating.FiniteColouredOccurrenceWord

namespace Alternating.InfiniteColouredOccurrenceWord

def restrictReference (Q : InfiniteColouredOccurrenceWord W Y)
    (hback : Q.backwardEdges ⊆ familyEdges Local) :
    InfiniteColouredOccurrenceWord W Local where
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hd : Q.direction i with
    | forward => simpa only [hd] using Q.actualEdge_spec i
    | backward =>
        apply hback
        refine ⟨⟨i, by simp [hd]⟩, ?_⟩
        simp [backwardEdge, actualEdge, hd]
  occurrence_injective := Q.occurrence_injective

theorem IsIntervalSafe.restrictReference
    {Q : InfiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hsub : Local ⊆ Y) (hback : Q.backwardEdges ⊆ familyEdges Local) :
    (Q.restrictReference hback).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    exact hQ.incoming_removed hxy (subwarp_edges_subset hsub hby)
  · intro x y b hxy hxb
    exact hQ.outgoing_removed hxy (subwarp_edges_subset hsub hxb)
  · intro p hp
    exact hQ.intervals p (hsub hp)
  · intro x y hxy
    refine ⟨?_, ?_⟩
    · rintro ⟨p, hp, hpy⟩
      exact (hQ.endpoint_pure hxy).1 ⟨p, hsub hp, hpy⟩
    · rintro ⟨p, hp, hpx⟩
      exact (hQ.endpoint_pure hxy).2 ⟨p, hsub hp, hpx⟩

end Alternating.InfiniteColouredOccurrenceWord

namespace ColouredSafeReverseReachability.CurrentSafeOccurrence

variable {s : V}

def restrictReference (A : CurrentSafeOccurrence W Y s)
    (hsub : Local ⊆ Y) (hback : A.backwardEdges ⊆ familyEdges Local) :
    CurrentSafeOccurrence W Local s :=
  match A with
  | .finite t Q hQ hfirst hlast =>
      .finite t (Q.restrictReference hback) (hQ.restrictReference hsub hback) hfirst hlast
  | .infinite Q hQ hfirst =>
      .infinite (Q.restrictReference hback) (hQ.restrictReference hsub hback) hfirst

@[simp] theorem restrictReference_forwardEdges (A : CurrentSafeOccurrence W Y s)
    (hsub : Local ⊆ Y) (hback : A.backwardEdges ⊆ familyEdges Local) :
    (A.restrictReference hsub hback).forwardEdges = A.forwardEdges := by
  cases A <;> rfl

@[simp] theorem restrictReference_backwardEdges (A : CurrentSafeOccurrence W Y s)
    (hsub : Local ⊆ Y) (hback : A.backwardEdges ⊆ familyEdges Local) :
    (A.restrictReference hsub hback).backwardEdges = A.backwardEdges := by
  cases A <;> rfl

@[simp] theorem restrictReference_vertexSet (A : CurrentSafeOccurrence W Y s)
    (hsub : Local ⊆ Y) (hback : A.backwardEdges ⊆ familyEdges Local) :
    (A.restrictReference hsub hback).vertexSet = A.vertexSet := by
  cases A <;> rfl

@[simp] theorem restrictReference_terminal (A : CurrentSafeOccurrence W Y s)
    (hsub : Local ⊆ Y) (hback : A.backwardEdges ⊆ familyEdges Local) :
    (A.restrictReference hsub hback).terminal? = A.terminal? := by
  cases A <;> rfl

theorem restrictReference_switchedEdges_subset (A : CurrentSafeOccurrence W Y s)
    (hsub : Local ⊆ Y) (hback : A.backwardEdges ⊆ familyEdges Local) :
    (A.restrictReference hsub hback).switchedEdges ⊆ A.switchedEdges := by
  intro e he
  rcases he with he | he
  · exact Or.inl ⟨subwarp_edges_subset hsub he.1, by simpa using he.2⟩
  · exact Or.inr (by simpa using he)

theorem backwardEdges_subset_of_avoids_discardedReference
    (A : CurrentSafeOccurrence W Y s)
    (havoid : Disjoint A.vertexSet (Gamma.vertexSet (Y \ Local))) :
    A.backwardEdges ⊆ familyEdges Local := by
  intro e he
  have hYedge : e ∈ familyEdges Y := by
    cases A with
    | finite t Q => exact Q.backwardEdges_subset_familyEdges he
    | infinite Q => exact Q.backwardEdges_subset_familyEdges he
  have hxA : e.1 ∈ A.vertexSet := by
    cases A with
    | finite t Q => exact (Q.backwardEdges_endpoints_mem_vertexSet he).1
    | infinite Q =>
        obtain ⟨i, rfl⟩ := he
        rw [Q.backwardEdge_eq]
        exact ⟨i.1 + 1, rfl⟩
  simp only [familyEdges, Set.mem_iUnion] at hYedge ⊢
  obtain ⟨p, hp, hep⟩ := hYedge
  have hpLocal : p ∈ Local := by
    by_contra hnot
    exact Set.disjoint_left.mp havoid hxA
      ⟨p, ⟨hp, hnot⟩, (p.edgeSet_subset_support_prod hep).1⟩
  exact ⟨p, hpLocal, hep⟩

end ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace ColouredSafeAmbientOccurrence

open ColouredSafeReverseReachability

variable {s : V}

theorem Valid.restrictReference {A : Occurrence Y s} (hA : Valid A)
    (hsub : Local ⊆ Y) (hback : A.backwardEdges ⊆ familyEdges Local) :
    Valid (A.restrictReference hsub hback) := by
  obtain ⟨W, hW, hfinite, hforward⟩ := hA
  exact ⟨W, hW, hfinite, by simpa using hforward⟩

#print axioms CurrentSafeOccurrence.restrictReference
#print axioms CurrentSafeOccurrence.restrictReference_switchedEdges_subset
#print axioms CurrentSafeOccurrence.backwardEdges_subset_of_avoids_discardedReference
#print axioms Valid.restrictReference

end ColouredSafeAmbientOccurrence
end Erdos599
