/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointStageCausality
import ErdosProblems.Erdos599.ColouredSafeEndpointLocalizationSemantics

/-!
# Promotion of roof-supported endpoint-pruned occurrences

Every local endpoint-pruned occurrence whose complete carrier is roofed
promotes to the actual limiting endpoint-pruned reference. Both coloured
relations and every chronological vertex are unchanged. Localization and
promotion are inverse on roof-supported occurrences; in particular the
promotion is injective and preserves finite switched reachability.
-/

noncomputable section

namespace Erdos599

open Set Cardinal DirectedPath Alternating Ladder Blueprint
open DWeb.KappaLadder.Deferred
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}
variable {W : Set Gamma.DPath} {s t : V} {e : Option V}

namespace Alternating.FiniteColouredOccurrenceWord

def retypeEndpointLimitReference
    (hL : HalfwayGeometry L) (Q : FiniteColouredOccurrenceWord W (stageReference hL a s e)) :
    FiniteColouredOccurrenceWord W (reference L.limitWarp s e) :=
  Q.retypeEdges Set.Subset.rfl (embedding hL a s e).familyEdges_subset

@[simp] theorem retypeEndpointLimitReference_forwardEdges
    (hL : HalfwayGeometry L) (Q : FiniteColouredOccurrenceWord W (stageReference hL a s e)) :
    (Q.retypeEndpointLimitReference hL).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeEndpointLimitReference_backwardEdges
    (hL : HalfwayGeometry L) (Q : FiniteColouredOccurrenceWord W (stageReference hL a s e)) :
    (Q.retypeEndpointLimitReference hL).backwardEdges = Q.backwardEdges := rfl

@[simp] theorem retypeEndpointLimitReference_vertexSet
    (hL : HalfwayGeometry L) (Q : FiniteColouredOccurrenceWord W (stageReference hL a s e)) :
    (Q.retypeEndpointLimitReference hL).vertexSet = Q.vertexSet := rfl

theorem IsIntervalSafe.retypeEndpointLimitReference
    (hL : HalfwayGeometry L) {Q : FiniteColouredOccurrenceWord W (stageReference hL a s e)}
    (hQ : Q.IsIntervalSafe) (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeEndpointLimitReference hL).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    exact hQ.incoming_removed hxy (incoming_edge_reflect hL hby
      (hRoof (Q.forwardEdges_endpoints_mem_vertexSet hxy).2))
  · intro x y b hxy hxb
    exact hQ.outgoing_removed hxy (outgoing_edge_reflect hL hxb
      (hRoof (Q.forwardEdges_endpoints_mem_vertexSet hxy).1) (hQ.endpoint_pure hxy).2)
  · exact (embedding hL a s e).edgeIntervals_global
      Q.backwardEdges_subset_familyEdges hQ.intervals
  · intro x y hxy
    have hends := Q.forwardEdges_endpoints_mem_vertexSet hxy
    exact ⟨fun hy ↦ (hQ.endpoint_pure hxy).1
      (initialSet_reflect_of_roof hL hy (hRoof hends.2)),
      fun hx ↦ (hQ.endpoint_pure hxy).2
        (terminalFrontier_reflect_of_roof hL hx (hRoof hends.1))⟩

end Alternating.FiniteColouredOccurrenceWord

namespace Alternating.InfiniteColouredOccurrenceWord

def retypeEndpointLimitReference
    (hL : HalfwayGeometry L) (Q : InfiniteColouredOccurrenceWord W (stageReference hL a s e)) :
    InfiniteColouredOccurrenceWord W (reference L.limitWarp s e) where
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hd : Q.direction i with
    | forward => simpa only [hd] using Q.actualEdge_spec i
    | backward =>
        apply (embedding hL a s e).familyEdges_subset
        simpa only [hd] using Q.actualEdge_spec i
  occurrence_injective := Q.occurrence_injective

@[simp] theorem retypeEndpointLimitReference_forwardEdges
    (hL : HalfwayGeometry L) (Q : InfiniteColouredOccurrenceWord W (stageReference hL a s e)) :
    (Q.retypeEndpointLimitReference hL).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeEndpointLimitReference_backwardEdges
    (hL : HalfwayGeometry L) (Q : InfiniteColouredOccurrenceWord W (stageReference hL a s e)) :
    (Q.retypeEndpointLimitReference hL).backwardEdges = Q.backwardEdges := rfl

@[simp] theorem retypeEndpointLimitReference_vertexSet
    (hL : HalfwayGeometry L) (Q : InfiniteColouredOccurrenceWord W (stageReference hL a s e)) :
    (Q.retypeEndpointLimitReference hL).vertexSet = Q.vertexSet := rfl

theorem IsIntervalSafe.retypeEndpointLimitReference
    (hL : HalfwayGeometry L) {Q : InfiniteColouredOccurrenceWord W (stageReference hL a s e)}
    (hQ : Q.IsIntervalSafe) (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeEndpointLimitReference hL).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    exact hQ.incoming_removed hxy (incoming_edge_reflect hL hby
      (hRoof (Q.forwardEdges_endpoints_mem_vertexSet hxy).2))
  · intro x y b hxy hxb
    exact hQ.outgoing_removed hxy (outgoing_edge_reflect hL hxb
      (hRoof (Q.forwardEdges_endpoints_mem_vertexSet hxy).1) (hQ.endpoint_pure hxy).2)
  · exact (embedding hL a s e).edgeIntervals_global
      Q.backwardEdges_subset_familyEdges hQ.intervals
  · intro x y hxy
    have hends := Q.forwardEdges_endpoints_mem_vertexSet hxy
    exact ⟨fun hy ↦ (hQ.endpoint_pure hxy).1
      (initialSet_reflect_of_roof hL hy (hRoof hends.2)),
      fun hx ↦ (hQ.endpoint_pure hxy).2
        (terminalFrontier_reflect_of_roof hL hx (hRoof hends.1))⟩

end Alternating.InfiniteColouredOccurrenceWord

namespace ColouredSafeReverseReachability.CurrentSafeOccurrence

def retypeEndpointLimitReference (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (stageReference hL a s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    CurrentSafeOccurrence W (reference L.limitWarp s e) s := by
  cases A with
  | infinite Q hsafe hfirst =>
      exact .infinite (Q.retypeEndpointLimitReference hL)
        (hsafe.retypeEndpointLimitReference hL hRoof) hfirst
  | finite t Q hsafe hfirst hlast =>
      exact .finite t (Q.retypeEndpointLimitReference hL)
        (hsafe.retypeEndpointLimitReference hL hRoof) hfirst hlast

@[simp] theorem retypeEndpointLimitReference_forwardEdges (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (stageReference hL a s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointLimitReference hL hRoof).forwardEdges = A.forwardEdges := by
  cases A <;> rfl

@[simp] theorem retypeEndpointLimitReference_backwardEdges (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (stageReference hL a s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointLimitReference hL hRoof).backwardEdges = A.backwardEdges := by
  cases A <;> rfl

@[simp] theorem retypeEndpointLimitReference_vertexSet (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (stageReference hL a s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointLimitReference hL hRoof).vertexSet = A.vertexSet := by
  cases A <;> rfl

@[simp] theorem retypeEndpointLimitReference_terminal? (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (stageReference hL a s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointLimitReference hL hRoof).terminal? = A.terminal? := by
  cases A <;> rfl

@[simp] theorem localize_promote (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (stageReference hL a s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointLimitReference hL hRoof).retypeEndpointStageReference hL
      (by simpa only [retypeEndpointLimitReference_vertexSet] using hRoof) = A := by
  cases A <;> rfl

@[simp] theorem promote_localize (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointStageReference hL hRoof).retypeEndpointLimitReference hL
      (by simpa only [retypeEndpointStageReference_vertexSet] using hRoof) = A := by
  cases A <;> rfl

theorem retypeEndpointLimitReference_injective (hL : HalfwayGeometry L) :
    Function.Injective
      (fun A : {A : CurrentSafeOccurrence W (stageReference hL a s e) s //
          A.vertexSet ⊆ Gamma.roof (L.frontier a)} ↦
        A.1.retypeEndpointLimitReference hL A.2) := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ h
  apply Subtype.ext
  have hlocal := congrArg
    (fun C : {C : CurrentSafeOccurrence W (reference L.limitWarp s e) s //
        C.vertexSet ⊆ Gamma.roof (L.frontier a)} ↦
      C.1.retypeEndpointStageReference hL C.2)
    (show (⟨A.retypeEndpointLimitReference hL hA,
        by simpa only [retypeEndpointLimitReference_vertexSet] using hA⟩ :
          {C : CurrentSafeOccurrence W (reference L.limitWarp s e) s //
            C.vertexSet ⊆ Gamma.roof (L.frontier a)}) =
      ⟨B.retypeEndpointLimitReference hL hB,
        by simpa only [retypeEndpointLimitReference_vertexSet] using hB⟩
      from Subtype.ext h)
  simpa only [localize_promote] using hlocal

theorem hasFiniteSwitchedPathTo_retypeEndpointLimitReference_iff
    (hL : HalfwayGeometry L) (A : CurrentSafeOccurrence W (stageReference hL a s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (htRoof : t ∈ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointLimitReference hL hRoof).HasFiniteSwitchedPathTo t ↔
      A.HasFiniteSwitchedPathTo t := by
  have h := hasFiniteSwitchedPathTo_retypeEndpointStageReference_iff hL
      (A.retypeEndpointLimitReference hL hRoof)
      (by simpa only [retypeEndpointLimitReference_vertexSet] using hRoof) htRoof
  simpa only [localize_promote] using h.symm

#print axioms retypeEndpointLimitReference
#print axioms localize_promote
#print axioms promote_localize
#print axioms retypeEndpointLimitReference_injective
#print axioms hasFiniteSwitchedPathTo_retypeEndpointLimitReference_iff

end ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace ColouredSafeAmbientOccurrence

open ColouredSafeReverseReachability

theorem Valid.retypeEndpointLimitReference (hL : HalfwayGeometry L)
    {A : Occurrence (stageReference hL a s e) s} (hA : Valid A)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    Valid (A.retypeEndpointLimitReference hL hRoof) := by
  obtain ⟨W, hW, hfinite, hEdges⟩ := hA
  exact ⟨W, hW, hfinite, by simpa only
    [CurrentSafeOccurrence.retypeEndpointLimitReference_forwardEdges] using hEdges⟩

#print axioms Valid.retypeEndpointLimitReference

end ColouredSafeAmbientOccurrence

end Erdos599
