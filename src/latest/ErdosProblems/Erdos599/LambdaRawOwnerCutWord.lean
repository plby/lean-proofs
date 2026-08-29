/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawOwnerSwitchRealization
import ErdosProblems.Erdos599.LambdaRawEdgeEntrySwitch

/-!
# The attached raw word stopped at its final cut-edge head

Only the final backward step is removed. Its freshness, literal partition
of backward edges, and actual endpoint at the edge head are all retained.
The suffix need not itself start at an auxiliary source.
-/

noncomputable section

namespace Erdos599.PopularAuxiliary.Input.RawOwnerAttachment

open Set DirectedPath Alternating

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable {L : PopularAuxiliary.Input Gamma I} {H : Gamma.DPath}
variable {p : FinitePath L.lambda.graph} (A : L.RawOwnerAttachment H p)

/-- The genuine attachment followed by the suffix's head-stopping word. -/
def entrySteps (u v : V) (hfinish : p.finish = .edge u v) : List (SignedEdge V) :=
  SignedEdge.forward (A.anchor, A.nextVertex) ::
    L.rawEdgeEntrySteps A.tail u v (A.tail_finish.trans hfinish)

theorem steps_eq_entry_append (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) :
    A.steps = A.entrySteps u v hfinish ++ [SignedEdge.backward (u, v)] := by
  have hne : u ≠ v := L.raw_familyEdge_ne
    (L.edgeNode_mem_familyEdges_of_start_in_source p hs
      (hfinish ▸ p.finish_mem_support))
  have htail : L.decodeProperSteps A.tail =
      L.rawEdgeEntrySteps A.tail u v (A.tail_finish.trans hfinish) ++
        [SignedEdge.backward (u, v)] := by
    rw [decodeProperSteps,
      L.decodeWalkSteps_eq_edgeEntry_append A.tail u v (A.tail_finish.trans hfinish),
      properSignedSteps_append]
    simp [rawEdgeEntrySteps, properSignedSteps, hne]
  simp only [steps, htail, entrySteps, List.cons_append]

theorem entrySteps_forwardEdges (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) :
    directedSignedEdgeSet .forward (A.entrySteps u v hfinish) = A.forwardEdges := by
  rw [← A.steps_forwardEdges, A.steps_eq_entry_append hs u v hfinish,
    directedSignedEdgeSet_append]
  simp [directedSignedEdgeSet]

theorem entrySteps_backward_partition (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) :
    L.representedEdges A.tail =
      directedSignedEdgeSet .backward (A.entrySteps u v hfinish) ∪ {(u, v)} := by
  rw [← A.steps_backwardEdges hs, A.steps_eq_entry_append hs u v hfinish,
    directedSignedEdgeSet_append]
  simp [directedSignedEdgeSet]

theorem entrySteps_nodup (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) (u v : V) (hfinish : p.finish = .edge u v) :
    (A.entrySteps u v hfinish).Nodup := by
  have h := A.steps_nodup hL hH hs
  rw [A.steps_eq_entry_append hs u v hfinish] at h
  exact (List.nodup_append.1 h).1

theorem entrySteps_omits_cut_edge (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) (u v : V) (hfinish : p.finish = .edge u v) :
    (u, v) ∉ directedSignedEdgeSet .backward (A.entrySteps u v hfinish) := by
  rintro ⟨s, hsEntry, hd, he⟩
  have hsEq : s = SignedEdge.backward (u, v) := by
    cases s with
    | mk edge direction =>
        cases hd
        cases he
        rfl
  have h := A.steps_nodup hL hH hs
  rw [A.steps_eq_entry_append hs u v hfinish] at h
  exact (List.nodup_append.1 h).2.2 s hsEntry
    (SignedEdge.backward (u, v)) (by simp) hsEq

/-- The head-stop backward relation lies in the actual cut-deleted,
whole-owner-deleted reference. -/
theorem entrySteps_backward_subset_cut_reference
    (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) (u v : V) (hfinish : p.finish = .edge u v)
    (C : Set (V × V))
    (hcut : ∀ e ∈ C, LambdaVertex.edge e.1 e.2 ∈ p.support → e = (u, v)) :
    directedSignedEdgeSet .backward (A.entrySteps u v hfinish) ⊆
      (L.familyEdges \ H.edgeSet) \ C := by
  intro e he
  have hrepresented : e ∈ L.representedEdges A.tail := by
    rw [A.entrySteps_backward_partition hs u v hfinish]
    exact Or.inl he
  refine ⟨A.backward_subset_ownerDeleted hH hrepresented, ?_⟩
  intro heC
  have heEq := hcut e heC (A.tail_support_subset hrepresented.1)
  exact A.entrySteps_omits_cut_edge hL hH hs u v hfinish (heEq ▸ he)

/-- The exact signed word ends at the head, not the exit, of the final gadget. -/
theorem entrySteps_runs (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) :
    RunsFromTo A.anchor v (A.entrySteps u v hfinish) := by
  have hexit : L.gadgetExit p.finish = some u := by rw [hfinish]; rfl
  have hrun := A.steps_runs hexit
  rw [A.steps_eq_entry_append hs u v hfinish] at hrun
  exact RunsFromTo.init_of_append_singleton hrun

/-- Signed balance after removing exactly the final backward edge. -/
theorem entrySteps_direction_balance
    (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) (u v : V) (hfinish : p.finish = .edge u v) (x : V) :
    edgeBalance A.forwardEdges x -
        edgeBalance (directedSignedEdgeSet .backward (A.entrySteps u v hfinish)) x =
      propInt (x = A.anchor) - propInt (x = v) := by
  have hF : Relator.BiUnique
      (fun a b ↦ (a, b) ∈ directedSignedEdgeSet .forward (A.entrySteps u v hfinish)) := by
    rw [A.entrySteps_forwardEdges hs u v hfinish]
    exact A.forwardEdges_biUnique hL hH
  have hsub : directedSignedEdgeSet .backward (A.entrySteps u v hfinish) ⊆
      L.familyEdges := by
    intro e he
    have hrepresented : e ∈ L.representedEdges A.tail := by
      rw [A.entrySteps_backward_partition hs u v hfinish]
      exact Or.inl he
    exact hrepresented.2
  have hB : Relator.BiUnique
      (fun a b ↦ (a, b) ∈ directedSignedEdgeSet .backward (A.entrySteps u v hfinish)) :=
    ⟨fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.1 (hsub h₁) (hsub h₂),
      fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.2 (hsub h₁) (hsub h₂)⟩
  simpa only [A.entrySteps_forwardEdges hs u v hfinish] using
    (A.entrySteps_runs hs u v hfinish).edgeBalance_forward_sub_backward
      (A.entrySteps_nodup hL hH hs u v hfinish) hF hB x

#print axioms entrySteps_backward_subset_cut_reference
#print axioms entrySteps_direction_balance

end Erdos599.PopularAuxiliary.Input.RawOwnerAttachment
