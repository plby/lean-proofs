/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeOccurrenceSemantics
import ErdosProblems.Erdos599.FiniteColouredOccurrenceReductionTransfer

/-!
# Forward-metadata-erased safe occurrences

An occurrence produced by the successive construction is indexed by the
finite-character forward warp which existed at its birth stage.  That index
is useful when proving switch semantics, but it is not part of the literal
route: the vertices, colours, and actual edges already determine the route.

This file retypes the forward colour into the ambient family of all directed
paths.  The resulting `Occurrence` contains no chosen forward warp.  Its
`Valid` predicate records only that its forward relation is covered by some
honest finite-character warp.  Thus validity is enough to recover the
existing relational switch semantics, but does not postulate an output warp
or make different choices of covering warp into different occurrences.
-/

noncomputable section

open Set

namespace Erdos599

namespace Alternating.InfiniteColouredOccurrenceWord

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {W U Y : Set Gamma.DPath}

/-- Retype only the forward-family parameter of an infinite occurrence.
The chronological word and both literal colour relations are unchanged. -/
def retypeForward (Q : InfiniteColouredOccurrenceWord W Y)
    (hforward : Q.forwardEdges ⊆ familyEdges U) :
    InfiniteColouredOccurrenceWord U Y where
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
    (Q : InfiniteColouredOccurrenceWord W Y)
    (hforward : Q.forwardEdges ⊆ familyEdges U) (i : ℕ) :
    (Q.retypeForward hforward).vertex i = Q.vertex i := rfl

@[simp] theorem retypeForward_direction
    (Q : InfiniteColouredOccurrenceWord W Y)
    (hforward : Q.forwardEdges ⊆ familyEdges U) (i : ℕ) :
    (Q.retypeForward hforward).direction i = Q.direction i := rfl

@[simp] theorem retypeForward_forwardEdges
    (Q : InfiniteColouredOccurrenceWord W Y)
    (hforward : Q.forwardEdges ⊆ familyEdges U) :
    (Q.retypeForward hforward).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeForward_backwardEdges
    (Q : InfiniteColouredOccurrenceWord W Y)
    (hforward : Q.forwardEdges ⊆ familyEdges U) :
    (Q.retypeForward hforward).backwardEdges = Q.backwardEdges := rfl

@[simp] theorem retypeForward_vertexSet
    (Q : InfiniteColouredOccurrenceWord W Y)
    (hforward : Q.forwardEdges ⊆ familyEdges U) :
    (Q.retypeForward hforward).vertexSet = Q.vertexSet := rfl

/-- Infinite interval safeness depends only on the two literal colour
relations, hence survives forward retyping. -/
theorem IsIntervalSafe.retypeForward
    {Q : InfiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hforward : Q.forwardEdges ⊆ familyEdges U) :
    (Q.retypeForward hforward).IsIntervalSafe := by
  exact {
    incoming_removed := hQ.incoming_removed
    outgoing_removed := hQ.outgoing_removed
    intervals := hQ.intervals
    endpoint_pure := hQ.endpoint_pure }

end Alternating.InfiniteColouredOccurrenceWord

namespace ColouredSafeReverseReachability.CurrentSafeOccurrence

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {current W Y : Set Gamma.DPath} {s t : V}

/-- Retype the forward family of either branch of a current safe occurrence.
No chronological data or safety content changes. -/
def retypeForward (A : CurrentSafeOccurrence current Y s)
    (hforward : A.forwardEdges ⊆ familyEdges W) :
    CurrentSafeOccurrence W Y s :=
  match A with
  | .infinite Q hQ hfirst =>
      .infinite (Q.retypeForward hforward) (hQ.retypeForward hforward) hfirst
  | .finite t Q hQ hfirst hlast =>
      .finite t (Q.retypeForward hforward) (hQ.retypeForward hforward)
        hfirst hlast

@[simp] theorem retypeForward_forwardEdges
    (A : CurrentSafeOccurrence current Y s)
    (hforward : A.forwardEdges ⊆ familyEdges W) :
    (A.retypeForward hforward).forwardEdges = A.forwardEdges := by
  cases A <;> rfl

@[simp] theorem retypeForward_backwardEdges
    (A : CurrentSafeOccurrence current Y s)
    (hforward : A.forwardEdges ⊆ familyEdges W) :
    (A.retypeForward hforward).backwardEdges = A.backwardEdges := by
  cases A <;> rfl

@[simp] theorem retypeForward_vertexSet
    (A : CurrentSafeOccurrence current Y s)
    (hforward : A.forwardEdges ⊆ familyEdges W) :
    (A.retypeForward hforward).vertexSet = A.vertexSet := by
  cases A <;> rfl

@[simp] theorem retypeForward_terminal?
    (A : CurrentSafeOccurrence current Y s)
    (hforward : A.forwardEdges ⊆ familyEdges W) :
    (A.retypeForward hforward).terminal? = A.terminal? := by
  cases A <;> rfl

@[simp] theorem retypeForward_switchedEdges
    (A : CurrentSafeOccurrence current Y s)
    (hforward : A.forwardEdges ⊆ familyEdges W) :
    (A.retypeForward hforward).switchedEdges = A.switchedEdges := by
  simp [switchedEdges]

end ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace ColouredSafeAmbientOccurrence

open DirectedPath Alternating
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {current Y : Set Gamma.DPath} {s t : V}

/-- A safe occurrence with its forward-warp index erased.  The ambient
forward family is a type-level container only; `Valid` below supplies the
honest finite-character covering warp when semantics are required. -/
abbrev Occurrence (Y : Set Gamma.DPath) (s : V) :=
  CurrentSafeOccurrence (Set.univ : Set Gamma.DPath) Y s

private theorem familyEdges_subset_univ
    (current : Set Gamma.DPath) :
    familyEdges current ⊆ familyEdges (Set.univ : Set Gamma.DPath) := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, _hp, hep⟩ := he
  exact ⟨p, Set.mem_univ p, hep⟩

/-- Forget the birth-stage forward warp while retaining the literal word. -/
def toAmbient (A : CurrentSafeOccurrence current Y s) : Occurrence Y s :=
  A.retypeForward
    (A.forwardEdges_subset_current.trans (familyEdges_subset_univ current))

@[simp] theorem toAmbient_forwardEdges
    (A : CurrentSafeOccurrence current Y s) :
    (toAmbient A).forwardEdges = A.forwardEdges := by
  simp [toAmbient]

@[simp] theorem toAmbient_backwardEdges
    (A : CurrentSafeOccurrence current Y s) :
    (toAmbient A).backwardEdges = A.backwardEdges := by
  simp [toAmbient]

@[simp] theorem toAmbient_vertexSet
    (A : CurrentSafeOccurrence current Y s) :
    (toAmbient A).vertexSet = A.vertexSet := by
  simp [toAmbient]

@[simp] theorem toAmbient_terminal?
    (A : CurrentSafeOccurrence current Y s) :
    (toAmbient A).terminal? = A.terminal? := by
  simp [toAmbient]

@[simp] theorem toAmbient_switchedEdges
    (A : CurrentSafeOccurrence current Y s) :
    (toAmbient A).switchedEdges = A.switchedEdges := by
  simp [toAmbient]

/-- Intrinsic realizability of the erased forward colour.  This remembers
only that all literal forward edges are covered by some honest
finite-character warp; it contains no chosen output of a switch. -/
def Valid (A : Occurrence Y s) : Prop :=
  ∃ W : Set Gamma.DPath, Gamma.IsWarp W ∧ Gamma.HasFiniteCharacter W ∧
    A.forwardEdges ⊆ familyEdges W

/-- Every occurrence produced over an honest finite-character forward warp
becomes valid after erasing that warp. -/
theorem toAmbient_valid (A : CurrentSafeOccurrence current Y s)
    (hcurrent : Gamma.IsWarp current)
    (hcurrentFinite : Gamma.HasFiniteCharacter current) :
    Valid (toAmbient A) := by
  refine ⟨current, hcurrent, hcurrentFinite, ?_⟩
  simpa using A.forwardEdges_subset_current

theorem vertexSet_countable (A : Occurrence Y s) :
    A.vertexSet.Countable := A.vertexSet_countable

theorem backwardEdges_countable (A : Occurrence Y s) :
    A.backwardEdges.Countable := A.backwardEdges_countable

theorem source_mem_vertexSet (A : Occurrence Y s) :
    s ∈ A.vertexSet := A.source_mem_vertexSet

/-- A valid erased finite occurrence has the same exact switch semantics as
any of its honest forward-warp presentations. -/
theorem Valid.exists_finiteWarp_of_terminal
    {A : Occurrence Y s} (hA : Valid A)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hterminal : A.terminal? = some t) (hne : s ≠ t)
    (hstart : s ∉ Gamma.vertexSet Y) (hfinish : t ∉ Gamma.vertexSet Y) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = A.switchedEdges ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.initialSet U = Gamma.initialSet Y ∪ {s} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y ∪ {t} := by
  obtain ⟨W, hW, hWfinite, hforward⟩ := hA
  let B : CurrentSafeOccurrence W Y s := A.retypeForward hforward
  have hBterminal : B.terminal? = some t := by
    simpa [B] using hterminal
  obtain ⟨U, hU, hUfinite, hUE, hUI, hUinitial, hUterminal⟩ :=
    B.exists_finiteWarp_of_terminal hW hWfinite hY hYfinite hBterminal
      hne hstart hfinish
  exact ⟨U, hU, hUfinite, by simpa [B] using hUE, hUI,
    hUinitial, hUterminal⟩

/-- A valid erased infinite occurrence likewise realizes an exact
finite-character one-source switch. -/
theorem Valid.exists_finiteWarp_of_infinite
    {A : Occurrence Y s} (hA : Valid A)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinfinite : A.terminal? = none) (hstart : s ∉ Gamma.vertexSet Y) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = A.switchedEdges ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.initialSet U = Gamma.initialSet Y ∪ {s} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y := by
  obtain ⟨W, hW, hWfinite, hforward⟩ := hA
  let B : CurrentSafeOccurrence W Y s := A.retypeForward hforward
  have hBinfinite : B.terminal? = none := by
    simpa [B] using hinfinite
  obtain ⟨U, hU, hUfinite, hUE, hUI, hUinitial, hUterminal⟩ :=
    B.exists_finiteWarp_of_infinite hW hWfinite hY hYfinite hBinfinite hstart
  exact ⟨U, hU, hUfinite, by simpa [B] using hUE, hUI,
    hUinitial, hUterminal⟩

#print axioms Alternating.InfiniteColouredOccurrenceWord.IsIntervalSafe.retypeForward
#print axioms ColouredSafeReverseReachability.CurrentSafeOccurrence.retypeForward
#print axioms toAmbient_valid
#print axioms Valid.exists_finiteWarp_of_terminal
#print axioms Valid.exists_finiteWarp_of_infinite

end ColouredSafeAmbientOccurrence

end Erdos599
