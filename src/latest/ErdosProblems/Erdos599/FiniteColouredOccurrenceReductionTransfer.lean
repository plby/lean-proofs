/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReverseReachability
import ErdosProblems.Erdos599.ColouredResidualPortReduction

/-!
# The first fixed-forward reduction of a reduced-warp safe word

A finite safe word constructed after a reducing switch has forward edges in
the union of the original forward and reference relations.  There are two
genuinely different cases.  If all of its forward edges are still original,
the literal word retypes to the original forward warp and preserves every
safety field.  Otherwise an inherited reference edge occurs once forward and,
by incidence removal, once backward.  The two opposite-colour occurrences are
the concrete cancellation pivot needed by a source-changing exchange proof.

No claim is made here that this pivot can be erased while preserving the same
source and terminal; that stronger target-preserving statement is false.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {W U Y : Set Gamma.DPath}

open ColouredResidualPortReduction

/-- Retype only the forward-warp parameter of a finite occurrence word.
The hypothesis is on the word's actual forward relation, rather than on all
edges of its former forward warp. -/
def retypeForward (Q : FiniteColouredOccurrenceWord U Y)
    (hforward : Q.forwardEdges ⊆ familyEdges W) :
    FiniteColouredOccurrenceWord W Y where
  length := Q.length
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hdir : Q.direction i with
    | forward =>
        apply hforward
        refine ⟨⟨i, hdir⟩, ?_⟩
        simp [forwardEdge, actualEdge, hdir]
    | backward =>
        simpa [hdir] using Q.actualEdge_spec i
  occurrence_injective := Q.occurrence_injective

@[simp] theorem retypeForward_vertex
    (Q : FiniteColouredOccurrenceWord U Y)
    (hforward : Q.forwardEdges ⊆ familyEdges W)
    (i : Fin (Q.length + 1)) :
    (Q.retypeForward hforward).vertex i = Q.vertex i := rfl

@[simp] theorem retypeForward_direction
    (Q : FiniteColouredOccurrenceWord U Y)
    (hforward : Q.forwardEdges ⊆ familyEdges W)
    (i : Fin Q.length) :
    (Q.retypeForward hforward).direction i = Q.direction i := rfl

@[simp] theorem retypeForward_forwardEdges
    (Q : FiniteColouredOccurrenceWord U Y)
    (hforward : Q.forwardEdges ⊆ familyEdges W) :
    (Q.retypeForward hforward).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeForward_backwardEdges
    (Q : FiniteColouredOccurrenceWord U Y)
    (hforward : Q.forwardEdges ⊆ familyEdges W) :
    (Q.retypeForward hforward).backwardEdges = Q.backwardEdges := rfl

/-- Literal interval safeness is unchanged by forward retyping once every
actual forward occurrence has the new ownership certificate. -/
theorem IsIntervalSafe.retypeForward
    {Q : FiniteColouredOccurrenceWord U Y} (hQ : Q.IsIntervalSafe)
    (hforward : Q.forwardEdges ⊆ familyEdges W) :
    (Q.retypeForward hforward).IsIntervalSafe := by
  exact {
    incoming_removed := hQ.incoming_removed
    outgoing_removed := hQ.outgoing_removed
    intervals := hQ.intervals
    endpoint_pure := hQ.endpoint_pure }

/-- Easy branch of reduction transfer: if a reduced-warp witness uses only
original forward edges and its terminal is still an original terminal, it is
already an original safely-reachable witness. -/
theorem mem_safelyReachable_of_forwardEdges_subset
    {s t : V} {Q : FiniteColouredOccurrenceWord U Y}
    (hQ : Q.IsIntervalSafe)
    (hforward : Q.forwardEdges ⊆ familyEdges W)
    (hfirst : Q.vertex 0 = s)
    (hlast : Q.vertex (Fin.last Q.length) = t)
    (ht : t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y) :
    t ∈ ColouredSafeReverseReachability.safelyReachable W Y s := by
  exact ⟨ht, Q.retypeForward hforward, hQ.retypeForward hforward,
    hfirst, hlast⟩

/-- Any actual edge used both forward and backward has two distinct
chronological occurrences of opposite colours. -/
theorem exists_oppositeOccurrences_of_mem_forwardEdges_inter_backwardEdges
    (Q : FiniteColouredOccurrenceWord U Y) {e : V × V}
    (heF : e ∈ Q.forwardEdges) (heR : e ∈ Q.backwardEdges) :
    ∃ i j : Fin Q.length,
      Q.direction i = .forward ∧ Q.direction j = .backward ∧
        Q.actualEdge i = e ∧ Q.actualEdge j = e ∧ i ≠ j := by
  rcases heF with ⟨i, hi⟩
  rcases heR with ⟨j, hj⟩
  refine ⟨i.1, j.1, i.2, Q.backwardIndex_direction j, ?_, ?_, ?_⟩
  · exact hi
  · exact hj
  · intro hij
    have hdir : Q.direction i.1 = Q.direction j.1 :=
      congrArg Q.direction hij
    rw [i.2, Q.backwardIndex_direction j] at hdir
    exact Direction.noConfusion hdir

/-- Hard branch of reduction transfer.  If every new-forward occurrence is
either original or a reference edge but the word is not wholly original,
then an inherited reference edge occurs in both colours.  The returned
indices expose the exact opposite-colour pair for subsequent word surgery. -/
theorem exists_inheritedReference_cancellationPivot
    {Q : FiniteColouredOccurrenceWord U Y} (hQ : Q.IsIntervalSafe)
    (hunion : Q.forwardEdges ⊆ familyEdges W ∪ familyEdges Y)
    (hnotOriginal : ¬ Q.forwardEdges ⊆ familyEdges W) :
    ∃ (e : V × V) (i j : Fin Q.length),
      e ∉ familyEdges W ∧ e ∈ familyEdges Y ∧
        Q.direction i = .forward ∧ Q.direction j = .backward ∧
        Q.actualEdge i = e ∧ Q.actualEdge j = e ∧ i ≠ j := by
  obtain ⟨e, heF, heNotW⟩ := Set.not_subset.mp hnotOriginal
  have heY : e ∈ familyEdges Y := (hunion heF).resolve_left heNotW
  have heR : e ∈ Q.backwardEdges := by
    rcases e with ⟨x, y⟩
    exact hQ.incoming_removed heF heY
  obtain ⟨i, j, hi, hj, hie, hje, hij⟩ :=
    Q.exists_oppositeOccurrences_of_mem_forwardEdges_inter_backwardEdges heF heR
  exact ⟨e, i, j, heNotW, heY, hi, hj, hie, hje, hij⟩

/-- Specialization to the honest residual reduction used by the finite
single-source dichotomy.  No global `U ⊆ W ∪ Y` premise is needed: the
reduction path's exact edge provenance supplies it. -/
theorem residualReduction_forwardEdges_subset_original_union_reference
    (H : FinitePath (residualPortDigraph W Y))
    {Q : FiniteColouredOccurrenceWord U Y}
    (hUE : familyEdges U ⊆
      (familyEdges W \ ColouredResidualPortReduction.backwardEdges H) ∪
        ColouredResidualPortReduction.forwardEdges H) :
    Q.forwardEdges ⊆ familyEdges W ∪ familyEdges Y := by
  intro e he
  rcases hUE (Q.forwardEdges_subset_familyEdges he) with heW | heY
  · exact Or.inl heW.1
  · exact Or.inr (ColouredResidualPortReduction.forwardEdges_subset_familyEdges H heY)

/-- Exact first case split for pulling a safe word back through an actual
residual reduction.  The left branch is already an original-forward word;
the right branch exposes the opposite-colour inherited occurrence which a
source-changing pair exchange must resolve. -/
theorem residualReduction_original_or_cancellationPivot
    (H : FinitePath (residualPortDigraph W Y))
    {Q : FiniteColouredOccurrenceWord U Y} (hQ : Q.IsIntervalSafe)
    (hUE : familyEdges U ⊆
      (familyEdges W \ ColouredResidualPortReduction.backwardEdges H) ∪
        ColouredResidualPortReduction.forwardEdges H) :
    Q.forwardEdges ⊆ familyEdges W ∨
      ∃ (e : V × V) (i j : Fin Q.length),
        e ∉ familyEdges W ∧ e ∈ familyEdges Y ∧
          Q.direction i = .forward ∧ Q.direction j = .backward ∧
          Q.actualEdge i = e ∧ Q.actualEdge j = e ∧ i ≠ j := by
  by_cases hOriginal : Q.forwardEdges ⊆ familyEdges W
  · exact Or.inl hOriginal
  · exact Or.inr (exists_inheritedReference_cancellationPivot hQ
      (residualReduction_forwardEdges_subset_original_union_reference H hUE)
      hOriginal)

#print axioms IsIntervalSafe.retypeForward
#print axioms mem_safelyReachable_of_forwardEdges_subset
#print axioms exists_inheritedReference_cancellationPivot
#print axioms residualReduction_original_or_cancellationPivot

end Erdos599.Alternating.FiniteColouredOccurrenceWord
