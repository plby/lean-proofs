/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawPortIncidence

/-!
# Fresh signed occurrences in a raw auxiliary path

Only individual self-loops are removed. No physical-vertex loop erasure is
performed. Auxiliary simplicity and unique head ports imply that every
remaining same-colour edge occurs once, including on proxy-starting paths.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary.Input

open Set DirectedPath Alternating

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

/-- Remove only signed self-loop steps, whose entry equals their exit. -/
def properSignedSteps (q : List (SignedEdge V)) : List (SignedEdge V) := by
  classical
  exact q.filter (fun s ↦ decide (s.edge.1 ≠ s.edge.2))

@[simp] theorem mem_properSignedSteps {s : SignedEdge V} {q : List (SignedEdge V)} :
    s ∈ properSignedSteps q ↔ s ∈ q ∧ s.edge.1 ≠ s.edge.2 := by
  classical
  simp [properSignedSteps]

@[simp] theorem properSignedSteps_append (q r : List (SignedEdge V)) :
    properSignedSteps (q ++ r) = properSignedSteps q ++ properSignedSteps r := by
  classical
  simp [properSignedSteps]

/-- Filtering a signed self-loop does not change either endpoint. -/
theorem RunsFromTo.filter_selfLoops {x y : V} {q : List (SignedEdge V)}
    (h : RunsFromTo x y q) : RunsFromTo x y (properSignedSteps q) := by
  classical
  induction h with
  | nil x => exact .nil x
  | @cons s y q h ih =>
      by_cases hne : s.edge.1 ≠ s.edge.2
      · simpa [properSignedSteps, hne] using RunsFromTo.cons s ih
      · have heq : s.entry = s.exit := by
          have he : s.edge.1 = s.edge.2 := not_not.mp hne
          cases hdir : s.direction <;> simp [SignedEdge.entry, SignedEdge.exit, hdir, he]
        simpa [properSignedSteps, hne, heq] using ih

variable (L : PopularAuxiliary.Input Gamma I)

/-- The proper raw signed word: repeated original vertices are retained. -/
def decodeProperSteps (p : FinitePath L.lambda.graph) : List (SignedEdge V) :=
  properSignedSteps (L.decodeWalkSteps p.walk)

private theorem gadgetSteps_direction {a : L.LV} {s : SignedEdge V}
    (hs : s ∈ L.gadgetSteps a) :
    s.direction = .backward ∧ a = .edge s.edge.1 s.edge.2 := by
  cases a with
  | old x => simp [gadgetSteps] at hs
  | edge x y =>
      have hseq : s = SignedEdge.backward (x, y) := by simpa [gadgetSteps] using hs
      subst s
      exact ⟨rfl, rfl⟩
  | proxy i => simp [gadgetSteps] at hs

private theorem connectorSteps_direction {a b : L.LV} {s : SignedEdge V}
    (hs : s ∈ L.connectorSteps a b) :
    s.direction = .forward ∧ L.chosenConnector? a b = some s.edge := by
  cases hchoice : L.chosenConnector? a b with
  | none => simp [connectorSteps, hchoice] at hs
  | some e =>
      have hseq : s = SignedEdge.forward e := by
        simpa [connectorSteps, hchoice] using hs
      subst s
      exact ⟨rfl, rfl⟩

private theorem proper_gadget_nodup (a : L.LV) :
    (properSignedSteps (L.gadgetSteps a)).Nodup := by
  have h : (L.gadgetSteps a).Nodup := by cases a <;> simp [gadgetSteps]
  exact h.filter _

private theorem proper_connector_nodup (a b : L.LV) :
    (properSignedSteps (L.connectorSteps a b)).Nodup := by
  have hnodup : (L.connectorSteps a b).Nodup := by
    cases h : L.chosenConnector? a b <;> simp [connectorSteps, h]
  exact hnodup.filter _

variable {L}

/-- Raw decoding is fresh in signed edges after deleting only self-loops.
The original-vertex trace need not be injective. -/
theorem HasBoundaryIncidence.decodeProperSteps_nodup
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph) :
    (L.decodeProperSteps p).Nodup := by
  have hwalk : ∀ {a b : L.LV} (q : Walk L.lambda.graph a b), q.IsPath →
      (properSignedSteps (L.decodeWalkSteps q)).Nodup := by
    intro a b q
    induction q with
    | nil =>
        intro _hq
        exact L.proper_gadget_nodup _
    | @cons a b c hab q ih =>
        intro hq
        have hpath : a ∉ q.support ∧ q.IsPath := by
          simpa only [Walk.IsPath, Walk.support_cons, List.nodup_cons] using hq
        rw [L.decodeWalkSteps_cons, properSignedSteps_append,
          properSignedSteps_append]
        apply List.nodup_append.2
        refine ⟨List.nodup_append.2 ⟨L.proper_gadget_nodup a,
          L.proper_connector_nodup a b, ?_⟩, ih hpath.2, ?_⟩
        · intro s hs t ht hst
          subst t
          have hsBack := L.gadgetSteps_direction (mem_properSignedSteps.1 hs).1
          have hsForw := L.connectorSteps_direction (mem_properSignedSteps.1 ht).1
          cases hsBack.1.symm.trans hsForw.1
        · intro s hs t ht hst
          subst t
          rcases List.mem_append.1 hs with hs | hs
          · obtain ⟨hback, hnode⟩ :=
              L.gadgetSteps_direction (mem_properSignedSteps.1 hs).1
            have hraw : s.edge ∈ directedSignedEdgeSet .backward
                (L.decodeWalkSteps q) :=
              ⟨s, (mem_properSignedSteps.1 ht).1, hback, rfl⟩
            rw [L.backwardEdges_decodeWalkSteps q] at hraw
            exact hpath.1 (hnode.symm ▸ hraw)
          · obtain ⟨hforw, hchoice⟩ :=
              L.connectorSteps_direction (mem_properSignedSteps.1 hs).1
            have hne := (mem_properSignedSteps.1 hs).2
            have hraw : s.edge ∈ directedSignedEdgeSet .forward
                (L.decodeWalkSteps q) :=
              ⟨s, (mem_properSignedSteps.1 ht).1, hforw, rfl⟩
            rw [L.forwardEdges_decodeWalkSteps q] at hraw
            obtain ⟨d, e, hde, hchoice'⟩ := hraw
            have hbe : b = e :=
              (hL.forward_head_port hab (L.chosenConnector?_eq_some hchoice) hne).unique
                (hL.forward_head_port (q.edgeSet_subset_adj hde)
                  (L.chosenConnector?_eq_some hchoice') hne)
            let tail : FinitePath L.lambda.graph := ⟨b, c, q, hpath.2⟩
            apply Alternating.FinitePath.no_incoming_edge_at_start tail d
            change (d, b) ∈ q.edgeSet
            simpa only [← hbe] using hde
  exact hwalk p.walk p.isPath

/-- Filtering signed self-loops filters each direction relation by the
same proper-edge predicate. -/
theorem directedSignedEdgeSet_properSignedSteps (d : Direction)
    (q : List (SignedEdge V)) :
    directedSignedEdgeSet d (properSignedSteps q) =
      {e | e ∈ directedSignedEdgeSet d q ∧ e.1 ≠ e.2} := by
  ext e
  constructor
  · rintro ⟨s, hs, hd, he⟩
    have hs' := mem_properSignedSteps.1 hs
    exact ⟨⟨s, hs'.1, hd, he⟩, he ▸ hs'.2⟩
  · rintro ⟨⟨s, hs, hd, he⟩, hne⟩
    exact ⟨s, mem_properSignedSteps.2 ⟨hs, he ▸ hne⟩, hd, he⟩

/-- The forward relation of the proper signed word is literally the
proper deterministic connector relation used by the local switch. -/
theorem decodeProperSteps_forwardEdges (p : FinitePath L.lambda.graph) :
    directedSignedEdgeSet .forward (L.decodeProperSteps p) =
      L.properSelectedConnectorEdges p := by
  rw [decodeProperSteps, directedSignedEdgeSet_properSignedSteps,
    L.forwardEdges_decodeWalkSteps p.walk]
  rfl

/-- Source-starting paths lose no backward gadget under the self-loop
filter, because every represented edge belongs to a genuine path. -/
theorem decodeProperSteps_backwardEdges (p : FinitePath L.lambda.graph)
    (hs : p.start ∈ L.lambda.source) :
    directedSignedEdgeSet .backward (L.decodeProperSteps p) =
      L.representedEdges p := by
  rw [decodeProperSteps, directedSignedEdgeSet_properSignedSteps,
    L.backwardEdges_decodeWalkSteps p.walk]
  ext e
  constructor
  · intro he
    exact ⟨he.1, L.edgeNode_mem_familyEdges_of_start_in_source p hs he.1⟩
  · intro he
    exact ⟨he.1, L.raw_familyEdge_ne he.2⟩

end PopularAuxiliary.Input
end Erdos599

#print axioms Erdos599.PopularAuxiliary.Input.RunsFromTo.filter_selfLoops
#print axioms Erdos599.PopularAuxiliary.Input.HasBoundaryIncidence.decodeProperSteps_nodup
#print axioms Erdos599.PopularAuxiliary.Input.decodeProperSteps_backwardEdges
