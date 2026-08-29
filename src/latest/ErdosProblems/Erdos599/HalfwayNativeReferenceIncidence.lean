/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReferenceTransport
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Native incidence transport through an interval reference embedding

A reference subpath embedding transports removed-edge intervals without any
finiteness assumption on the global owners.  To transport the two incidence
clauses of a native coloured occurrence, it is enough that every global
reference contact at an endpoint of an inserted forward edge is already a
local-reference contact.  Local endpoint purity then supplies a local
incoming/outgoing edge, and biuniqueness in the global warp identifies it
with the given global edge.

This file deliberately separates that exact incidence condition from the
post-closure geometry which must prove it.  In particular it does not infer
contact confinement merely from roof containment.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath Alternating Blueprint

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace Blueprint.ReferenceSubpathEmbedding

variable {Local Global : Set Gamma.DPath}

/-- The only contacts relevant to native incidence transport are endpoints
of literal inserted forward edges. -/
def ForwardContactConfined
    (_E : ReferenceSubpathEmbedding Gamma Local Global)
    (F : Set (V × V)) : Prop :=
  ∀ {x y}, (x, y) ∈ F →
    (x ∈ Gamma.vertexSet Global → x ∈ Gamma.vertexSet Local) ∧
      (y ∈ Gamma.vertexSet Global → y ∈ Gamma.vertexSet Local)

theorem incoming_local_of_forwardContactConfined
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (hLocal : Gamma.IsWarp Local) {F : Set (V × V)}
    (hconfined : E.ForwardContactConfined F)
    (hpure : ∀ {x y}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Local ∧ x ∉ Gamma.terminalFrontier Local)
    {x b y : V} (hxy : (x, y) ∈ F)
    (hby : (b, y) ∈ familyEdges Global) :
    (b, y) ∈ familyEdges Local := by
  have hyGlobal : y ∈ Gamma.vertexSet Global :=
    (familyEdges_subset_vertexSet_prod Global hby).2
  have hyLocal : y ∈ Gamma.vertexSet Local :=
    (hconfined hxy).2 hyGlobal
  have hyIncoming : HasIncoming (familyEdges Local) y := by
    by_contra hnone
    apply (hpure hxy).1
    rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
      hLocal]
    exact ⟨hyLocal, hnone⟩
  obtain ⟨c, hcy⟩ := hyIncoming
  have hcb : c = b :=
    (IsWarp.familyEdges_biUnique E.global_isWarp).1
      (E.familyEdges_subset hcy) hby
  simpa only [hcb] using hcy

theorem outgoing_local_of_forwardContactConfined
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (hLocal : Gamma.IsWarp Local) {F : Set (V × V)}
    (hconfined : E.ForwardContactConfined F)
    (hpure : ∀ {x y}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Local ∧ x ∉ Gamma.terminalFrontier Local)
    {x y b : V} (hxy : (x, y) ∈ F)
    (hxb : (x, b) ∈ familyEdges Global) :
    (x, b) ∈ familyEdges Local := by
  have hxGlobal : x ∈ Gamma.vertexSet Global :=
    (familyEdges_subset_vertexSet_prod Global hxb).1
  have hxLocal : x ∈ Gamma.vertexSet Local :=
    (hconfined hxy).1 hxGlobal
  have hxOutgoing : HasOutgoing (familyEdges Local) x := by
    by_contra hnone
    apply (hpure hxy).2
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
      hLocal]
    exact ⟨hxLocal, hnone⟩
  obtain ⟨c, hxc⟩ := hxOutgoing
  have hcb : c = b :=
    (IsWarp.familyEdges_biUnique E.global_isWarp).2
      (E.familyEdges_subset hxc) hxb
  simpa only [hcb] using hxc

theorem endpointPure_global_of_forwardContactConfined
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (hLocal : Gamma.IsWarp Local) {F : Set (V × V)}
    (hconfined : E.ForwardContactConfined F)
    (hpure : ∀ {x y}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Local ∧ x ∉ Gamma.terminalFrontier Local) :
    ∀ {x y}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Global ∧ x ∉ Gamma.terminalFrontier Global := by
  intro x y hxy
  constructor
  · intro hyInitial
    rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
      E.global_isWarp] at hyInitial
    have hyLocal : y ∈ Gamma.vertexSet Local :=
      (hconfined hxy).2 hyInitial.1
    have hyIncoming : HasIncoming (familyEdges Local) y := by
      by_contra hnone
      apply (hpure hxy).1
      rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
        hLocal]
      exact ⟨hyLocal, hnone⟩
    obtain ⟨b, hby⟩ := hyIncoming
    exact hyInitial.2 ⟨b, E.familyEdges_subset hby⟩
  · intro hxTerminal
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
      E.global_isWarp] at hxTerminal
    have hxLocal : x ∈ Gamma.vertexSet Local :=
      (hconfined hxy).1 hxTerminal.1
    have hxOutgoing : HasOutgoing (familyEdges Local) x := by
      by_contra hnone
      apply (hpure hxy).2
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
        hLocal]
      exact ⟨hxLocal, hnone⟩
    obtain ⟨b, hxb⟩ := hxOutgoing
    exact hxTerminal.2 ⟨b, E.familyEdges_subset hxb⟩

end Blueprint.ReferenceSubpathEmbedding

namespace Alternating.FiniteColouredOccurrenceWord

variable {W Local Global : Set Gamma.DPath}

/-- Retype a finite native word along a reference subpath embedding. -/
def retypeReferenceEmbedding
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (Q : FiniteColouredOccurrenceWord W Local) :
    FiniteColouredOccurrenceWord W Global :=
  Q.retypeEdges Set.Subset.rfl E.familyEdges_subset

@[simp] theorem retypeReferenceEmbedding_forwardEdges
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (Q : FiniteColouredOccurrenceWord W Local) :
    (Q.retypeReferenceEmbedding E).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeReferenceEmbedding_backwardEdges
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (Q : FiniteColouredOccurrenceWord W Local) :
    (Q.retypeReferenceEmbedding E).backwardEdges = Q.backwardEdges := rfl

@[simp] theorem retypeReferenceEmbedding_vertexSet
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (Q : FiniteColouredOccurrenceWord W Local) :
    (Q.retypeReferenceEmbedding E).vertexSet = Q.vertexSet := rfl

/-- Forward-contact confinement is exactly sufficient for finite native
safeness to pass from a local interval reference to arbitrary global owners. -/
theorem IsIntervalSafe.retypeReferenceEmbedding
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (hLocal : Gamma.IsWarp Local)
    {Q : FiniteColouredOccurrenceWord W Local} (hQ : Q.IsIntervalSafe)
    (hconfined : E.ForwardContactConfined Q.forwardEdges) :
    (Q.retypeReferenceEmbedding E).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    change (x, y) ∈ Q.forwardEdges at hxy
    change (b, y) ∈ Q.backwardEdges
    exact hQ.incoming_removed hxy
      (E.incoming_local_of_forwardContactConfined hLocal hconfined
        hQ.endpoint_pure hxy hby)
  · intro x y b hxy hxb
    change (x, y) ∈ Q.forwardEdges at hxy
    change (x, b) ∈ Q.backwardEdges
    exact hQ.outgoing_removed hxy
      (E.outgoing_local_of_forwardContactConfined hLocal hconfined
        hQ.endpoint_pure hxy hxb)
  · exact E.edgeIntervals_global Q.backwardEdges_subset_familyEdges hQ.intervals
  · exact E.endpointPure_global_of_forwardContactConfined hLocal hconfined
      hQ.endpoint_pure

end Alternating.FiniteColouredOccurrenceWord

namespace Alternating.InfiniteColouredOccurrenceWord

variable {W Local Global : Set Gamma.DPath}

/-- Infinite reference retyping, preserving the literal word. -/
def retypeReferenceEmbedding
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (Q : InfiniteColouredOccurrenceWord W Local) :
    InfiniteColouredOccurrenceWord W Global where
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hdir : Q.direction i with
    | forward => simpa only [hdir] using Q.actualEdge_spec i
    | backward =>
        exact E.familyEdges_subset (by simpa only [hdir] using Q.actualEdge_spec i)
  occurrence_injective := Q.occurrence_injective

@[simp] theorem retypeReferenceEmbedding_forwardEdges
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (Q : InfiniteColouredOccurrenceWord W Local) :
    (Q.retypeReferenceEmbedding E).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeReferenceEmbedding_backwardEdges
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (Q : InfiniteColouredOccurrenceWord W Local) :
    (Q.retypeReferenceEmbedding E).backwardEdges = Q.backwardEdges := rfl

@[simp] theorem retypeReferenceEmbedding_vertexSet
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (Q : InfiniteColouredOccurrenceWord W Local) :
    (Q.retypeReferenceEmbedding E).vertexSet = Q.vertexSet := rfl

/-- Infinite native safeness obeys the same exact incidence criterion. -/
theorem IsIntervalSafe.retypeReferenceEmbedding
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (hLocal : Gamma.IsWarp Local)
    {Q : InfiniteColouredOccurrenceWord W Local} (hQ : Q.IsIntervalSafe)
    (hconfined : E.ForwardContactConfined Q.forwardEdges) :
    (Q.retypeReferenceEmbedding E).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    change (x, y) ∈ Q.forwardEdges at hxy
    change (b, y) ∈ Q.backwardEdges
    exact hQ.incoming_removed hxy
      (E.incoming_local_of_forwardContactConfined hLocal hconfined
        hQ.endpoint_pure hxy hby)
  · intro x y b hxy hxb
    change (x, y) ∈ Q.forwardEdges at hxy
    change (x, b) ∈ Q.backwardEdges
    exact hQ.outgoing_removed hxy
      (E.outgoing_local_of_forwardContactConfined hLocal hconfined
        hQ.endpoint_pure hxy hxb)
  · exact E.edgeIntervals_global Q.backwardEdges_subset_familyEdges hQ.intervals
  · exact E.endpointPure_global_of_forwardContactConfined hLocal hconfined
      hQ.endpoint_pure

end Alternating.InfiniteColouredOccurrenceWord

#print axioms Blueprint.ReferenceSubpathEmbedding.endpointPure_global_of_forwardContactConfined
#print axioms Alternating.FiniteColouredOccurrenceWord.IsIntervalSafe.retypeReferenceEmbedding
#print axioms Alternating.InfiniteColouredOccurrenceWord.IsIntervalSafe.retypeReferenceEmbedding

end Erdos599
