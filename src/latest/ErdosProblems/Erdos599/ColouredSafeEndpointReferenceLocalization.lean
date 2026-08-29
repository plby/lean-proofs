/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointStageReference

/-!
# Literal localization of endpoint-pruned safe occurrences

Roofed removed edges belong to the actual stage prefixes selected by their
limiting owners. All chronological data and both colour relations remain
unchanged. Incidence removal, interval convexity and endpoint purity are
proved for that local reference; its finite character is not assumed.
-/

noncomputable section

namespace Erdos599

open Set Cardinal DirectedPath Alternating Ladder Blueprint
open DWeb.KappaLadder.Deferred
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}
variable {W : Set Gamma.DPath} {s : V} {e : Option V}

namespace Alternating.FiniteColouredOccurrenceWord

theorem backwardEdges_subset_endpointStage_of_roof
    (hL : HalfwayGeometry L) (Q : FiniteColouredOccurrenceWord W (reference L.limitWarp s e))
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    Q.backwardEdges ⊆ familyEdges (stageReference hL a s e) := by
  intro edge he
  exact incoming_edge_reflect hL (Q.backwardEdges_subset_familyEdges he)
    (hRoof (Q.backwardEdges_endpoints_mem_vertexSet he).2)

def retypeEndpointStageReference
    (hL : HalfwayGeometry L) (Q : FiniteColouredOccurrenceWord W (reference L.limitWarp s e))
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    FiniteColouredOccurrenceWord W (stageReference hL a s e) where
  length := Q.length
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hd : Q.direction i with
    | forward => simpa only [hd] using Q.actualEdge_spec i
    | backward =>
        apply incoming_edge_reflect hL
          (by simpa only [hd] using Q.actualEdge_spec i)
        exact hRoof ⟨i.castSucc, rfl⟩
  occurrence_injective := Q.occurrence_injective

@[simp] theorem retypeEndpointStageReference_forwardEdges
    (hL : HalfwayGeometry L) (Q : FiniteColouredOccurrenceWord W (reference L.limitWarp s e))
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeEndpointStageReference hL hRoof).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeEndpointStageReference_backwardEdges
    (hL : HalfwayGeometry L) (Q : FiniteColouredOccurrenceWord W (reference L.limitWarp s e))
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeEndpointStageReference hL hRoof).backwardEdges = Q.backwardEdges := rfl

@[simp] theorem retypeEndpointStageReference_vertexSet
    (hL : HalfwayGeometry L) (Q : FiniteColouredOccurrenceWord W (reference L.limitWarp s e))
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeEndpointStageReference hL hRoof).vertexSet = Q.vertexSet := rfl

theorem IsIntervalSafe.retypeEndpointStageReference
    (hL : HalfwayGeometry L) {Q : FiniteColouredOccurrenceWord W (reference L.limitWarp s e)}
    (hQ : Q.IsIntervalSafe) (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeEndpointStageReference hL hRoof).IsIntervalSafe := by
  have hR := Q.backwardEdges_subset_endpointStage_of_roof hL hRoof
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    exact hQ.incoming_removed hxy ((embedding hL a s e).familyEdges_subset hby)
  · intro x y b hxy hxb
    exact hQ.outgoing_removed hxy ((embedding hL a s e).familyEdges_subset hxb)
  · exact (embedding hL a s e).edgeIntervals_local hR hQ.intervals
  · exact endpointPure_local_of_removed_edges_local hR hQ.outgoing_removed hQ.endpoint_pure

end Alternating.FiniteColouredOccurrenceWord

namespace Alternating.InfiniteColouredOccurrenceWord

theorem backwardEdges_subset_endpointStage_of_roof
    (hL : HalfwayGeometry L) (Q : InfiniteColouredOccurrenceWord W (reference L.limitWarp s e))
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    Q.backwardEdges ⊆ familyEdges (stageReference hL a s e) := by
  intro edge he
  exact incoming_edge_reflect hL (Q.backwardEdges_subset_familyEdges he)
    (hRoof (Q.backwardEdges_endpoints_mem_vertexSet he).2)

def retypeEndpointStageReference
    (hL : HalfwayGeometry L) (Q : InfiniteColouredOccurrenceWord W (reference L.limitWarp s e))
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    InfiniteColouredOccurrenceWord W (stageReference hL a s e) where
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hd : Q.direction i with
    | forward => simpa only [hd] using Q.actualEdge_spec i
    | backward =>
        apply incoming_edge_reflect hL
          (by simpa only [hd] using Q.actualEdge_spec i)
        exact hRoof ⟨i, rfl⟩
  occurrence_injective := Q.occurrence_injective

@[simp] theorem retypeEndpointStageReference_forwardEdges
    (hL : HalfwayGeometry L) (Q : InfiniteColouredOccurrenceWord W (reference L.limitWarp s e))
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeEndpointStageReference hL hRoof).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeEndpointStageReference_backwardEdges
    (hL : HalfwayGeometry L) (Q : InfiniteColouredOccurrenceWord W (reference L.limitWarp s e))
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeEndpointStageReference hL hRoof).backwardEdges = Q.backwardEdges := rfl

@[simp] theorem retypeEndpointStageReference_vertexSet
    (hL : HalfwayGeometry L) (Q : InfiniteColouredOccurrenceWord W (reference L.limitWarp s e))
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeEndpointStageReference hL hRoof).vertexSet = Q.vertexSet := rfl

theorem IsIntervalSafe.retypeEndpointStageReference
    (hL : HalfwayGeometry L) {Q : InfiniteColouredOccurrenceWord W (reference L.limitWarp s e)}
    (hQ : Q.IsIntervalSafe) (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeEndpointStageReference hL hRoof).IsIntervalSafe := by
  have hR := Q.backwardEdges_subset_endpointStage_of_roof hL hRoof
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    exact hQ.incoming_removed hxy ((embedding hL a s e).familyEdges_subset hby)
  · intro x y b hxy hxb
    exact hQ.outgoing_removed hxy ((embedding hL a s e).familyEdges_subset hxb)
  · exact (embedding hL a s e).edgeIntervals_local hR hQ.intervals
  · exact endpointPure_local_of_removed_edges_local hR hQ.outgoing_removed hQ.endpoint_pure

end Alternating.InfiniteColouredOccurrenceWord

namespace ColouredSafeReverseReachability.CurrentSafeOccurrence

def retypeEndpointStageReference (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    CurrentSafeOccurrence W (stageReference hL a s e) s := by
  cases A with
  | infinite Q hsafe hfirst =>
      exact .infinite (Q.retypeEndpointStageReference hL hRoof)
        (hsafe.retypeEndpointStageReference hL hRoof) hfirst
  | finite t Q hsafe hfirst hlast =>
      exact .finite t (Q.retypeEndpointStageReference hL hRoof)
        (hsafe.retypeEndpointStageReference hL hRoof) hfirst hlast

@[simp] theorem retypeEndpointStageReference_forwardEdges (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointStageReference hL hRoof).forwardEdges = A.forwardEdges := by
  cases A <;> rfl

@[simp] theorem retypeEndpointStageReference_backwardEdges (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointStageReference hL hRoof).backwardEdges = A.backwardEdges := by
  cases A <;> rfl

@[simp] theorem retypeEndpointStageReference_vertexSet (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointStageReference hL hRoof).vertexSet = A.vertexSet := by
  cases A <;> rfl

@[simp] theorem retypeEndpointStageReference_terminal? (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeEndpointStageReference hL hRoof).terminal? = A.terminal? := by
  cases A <;> rfl

#print axioms retypeEndpointStageReference
#print axioms retypeEndpointStageReference_forwardEdges
#print axioms retypeEndpointStageReference_backwardEdges
#print axioms retypeEndpointStageReference_vertexSet
#print axioms retypeEndpointStageReference_terminal?

end ColouredSafeReverseReachability.CurrentSafeOccurrence

end Erdos599
