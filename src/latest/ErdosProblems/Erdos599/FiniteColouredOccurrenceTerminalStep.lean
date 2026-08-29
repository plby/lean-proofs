/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceAppend
import ErdosProblems.Erdos599.FiniteColouredOccurrenceSwitch
import ErdosProblems.Erdos599.SafeSwitchingRelationalContactStep

/-!
# Terminal forward steps for finite coloured occurrence words

This file supplies the zero-transition word and the terminal Rule-1 step.
When the new forward fragment finishes outside the reference warp, no new
backward interval is needed: the conditional terminal-contact obligation is
vacuous.  The resulting safeness certificate is constructed from the literal
contact geometry rather than stored as an additional generation field.
-/

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- The occurrence word with one vertex and no transitions. -/
def emptyAt (s : V) : FiniteColouredOccurrenceWord W Y where
  length := 0
  vertex := fun _ ↦ s
  direction := fun i ↦ Fin.elim0 i
  actualEdge_spec := fun i ↦ Fin.elim0 i
  occurrence_injective := fun i ↦ Fin.elim0 i

@[simp] theorem emptyAt_length (s : V) :
    (emptyAt (W := W) (Y := Y) s).length = 0 := rfl

@[simp] theorem emptyAt_vertex (s : V)
    (i : Fin ((emptyAt (W := W) (Y := Y) s).length + 1)) :
    (emptyAt (W := W) (Y := Y) s).vertex i = s := rfl

@[simp] theorem emptyAt_first (s : V) :
    (emptyAt (W := W) (Y := Y) s).vertex 0 = s := rfl

@[simp] theorem emptyAt_last (s : V) :
    (emptyAt (W := W) (Y := Y) s).vertex
      (Fin.last (emptyAt (W := W) (Y := Y) s).length) = s := rfl

@[simp] theorem emptyAt_vertexSet (s : V) :
    (emptyAt (W := W) (Y := Y) s).vertexSet = {s} := by
  ext x
  simp [vertexSet, emptyAt]

@[simp] theorem emptyAt_forwardEdges (s : V) :
    (emptyAt (W := W) (Y := Y) s).forwardEdges = ∅ := by
  ext e
  constructor
  · rintro ⟨⟨i, _⟩, _⟩
    exact Fin.elim0 i
  · simp

@[simp] theorem emptyAt_backwardEdges (s : V) :
    (emptyAt (W := W) (Y := Y) s).backwardEdges = ∅ := by
  ext e
  constructor
  · rintro ⟨⟨i, _⟩, _⟩
    exact Fin.elim0 i
  · simp

/-- The empty word is interval-safe without any hypothesis on either warp. -/
theorem emptyAt_isIntervalSafe (s : V) :
    (emptyAt (W := W) (Y := Y) s).IsIntervalSafe := by
  constructor
  · simp
  · simp
  · intro p hp
    left
    simp
  · simp

/-- Append a terminal forward fragment.  Its finish lies outside the
reference carrier, so the terminal contact condition uses no new backward
edge.  All exact word, endpoint, carrier, and edge equations are those of
`appendForwardPath`. -/
theorem IsIntervalSafe.appendForwardPath_of_terminal_offReference
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (p : FinitePath Gamma.graph)
    (hjoin : Q.vertex (Fin.last Q.length) = p.start)
    (hp : p.edgeSet ⊆ familyEdges W)
    (hfresh : Disjoint p.edgeSet Q.forwardEdges)
    (hfinishOff : p.finish ∉ Gamma.vertexSet Y)
    (hstart : p.start ∈ Gamma.vertexSet Y →
      HasOutgoing Q.backwardEdges p.start)
    (hcontact : p.support ∩ Gamma.vertexSet Y ⊆
      {p.start, p.finish} ∪ removedInterior Q.backwardEdges) :
    (Q.appendForwardPath p hjoin hp hfresh).IsIntervalSafe := by
  let Q' := Q.appendForwardPath p hjoin hp hfresh
  have hQ'forward : Q'.forwardEdges = Q.forwardEdges ∪ p.edgeSet :=
    Q.appendForwardPath_forwardEdges p hjoin hp hfresh
  have hQ'back : Q'.backwardEdges = Q.backwardEdges :=
    Q.appendForwardPath_backwardEdges p hjoin hp hfresh
  have hfinish : p.finish ∈ Gamma.vertexSet Y → HasIncoming (∅ : Set (V × V)) p.finish :=
    fun hv ↦ False.elim (hfinishOff hv)
  have hnewInc := new_forward_conflicting_edges_removed hY
    Q.backwardEdges_subset_familyEdges (Set.empty_subset _) p hstart hfinish hcontact
  have hnewPure : ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y :=
    new_forward_endpoint_pure hY hYfin
      Q.backwardEdges_subset_familyEdges (Set.empty_subset _)
      p hstart hfinish hcontact
  constructor
  · intro a b x hax hbx
    rw [hQ'forward] at hax
    rw [hQ'back]
    exact hax.elim (fun h ↦ hQ.incoming_removed h hbx)
      (fun h ↦ by simpa using hnewInc.1 h hbx)
  · intro x a b hxa hxb
    rw [hQ'forward] at hxa
    rw [hQ'back]
    exact hxa.elim (fun h ↦ hQ.outgoing_removed h hxb)
      (fun h ↦ by simpa using hnewInc.2 h hxb)
  · intro r hrY
    rw [hQ'back]
    exact hQ.intervals r hrY
  · intro x y hxy
    rw [hQ'forward] at hxy
    exact hxy.elim (fun h ↦ hQ.endpoint_pure h) (fun h ↦ hnewPure h)

#print axioms emptyAt_isIntervalSafe
#print axioms IsIntervalSafe.appendForwardPath_of_terminal_offReference

end Erdos599.Alternating.FiniteColouredOccurrenceWord
