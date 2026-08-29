/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayIndexedRelationScheduler
import ErdosProblems.Erdos599.DeferredLadderRoofTransport

/-!
# Roof and closure transport for indexed half-way relation limits

The indexed scheduler changes its ladder frontier and closing set at every
successor.  Relation limits forget those parameters, but their carrier is
still exactly the union of the stage real carriers.  Deferred ladder
chronology therefore puts that union below every upper-bound frontier, and
monotonicity of the closing family puts it in the corresponding closing set.

These are genuine moving-stage consequences.  No fixed slice, global
closing set, or additional limit-boundary provider is assumed.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor
namespace ResolutionChain

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}
variable {persistent B : Set V}
variable {L : Gamma.KappaLadder theta}
variable {closedStage : Ladder.Stage theta → Set V}
variable {I : Type v} [LinearOrder I] [Nonempty I]

/-- Ordinary roofs of deferred-ladder frontiers are monotone in the stage. -/
theorem roof_frontier_mono_of_deferredLegal
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a b : Ladder.Stage theta} (hab : a ≤ b) :
    Gamma.roof (L.frontier a) ⊆ Gamma.roof (L.frontier b) := by
  rcases hab.lt_or_eq with hab | rfl
  · exact Gamma.roof_cut (hL.frontierChronology hab)
  · exact Set.Subset.rfl

/-- The real carrier union of an indexed scheduler chain is roofed by any
upper bound of its actual ladder indices. -/
theorem realVertexLimit_subset_roof_frontier
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := L.frontier) (closure := closedStage) I)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Ladder.Stage theta}
    (hupper : ∀ i, (C.stage i).stageIndex ≤ a) :
    C.toIndexedRealExtensionChain.realVertexLimit ⊆
      Gamma.roof (L.frontier a) := by
  intro x hx
  change x ∈ ⋃ i, (C.stage i).blueprint.realPart.vertices at hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
  have hxStage : x ∈ (C.stage i).blueprint.vertexSet := by
    simpa only [realPart_vertices] using hxi
  have hxRoof : x ∈ Gamma.roof (L.frontier (C.stage i).stageIndex) :=
    (C.stage i).isBlueprint.vertices_roofed hxStage
  exact roof_frontier_mono_of_deferredLegal hL (hupper i) hxRoof

/-- The same carrier union lies in every monotone closing set at an upper
bound of the actual scheduler indices. -/
theorem realVertexLimit_subset_closedStage
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := L.frontier) (closure := closedStage) I)
    (hclosed : Monotone closedStage)
    {a : Ladder.Stage theta}
    (hupper : ∀ i, (C.stage i).stageIndex ≤ a) :
    C.toIndexedRealExtensionChain.realVertexLimit ⊆ closedStage a := by
  intro x hx
  change x ∈ ⋃ i, (C.stage i).blueprint.realPart.vertices at hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
  have hxStage : x ∈ (C.stage i).blueprint.vertexSet := by
    simpa only [realPart_vertices] using hxi
  exact hclosed (hupper i) ((C.stage i).isBlueprint.vertices_closed hxStage)

/-- Concrete roof field for the proper eventual-edge relation limit. -/
theorem eventualRelationBlueprint_vertices_roofed
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := L.frontier) (closure := closedStage) I)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Ladder.Stage theta}
    (hupper : ∀ i, (C.stage i).stageIndex ≤ a) :
    C.toIndexedRealExtensionChain.eventualRelationBlueprint.vertexSet ⊆
      Gamma.roof (L.frontier a) := by
  rw [C.toIndexedRealExtensionChain.eventualRelationBlueprint_vertexSet]
  exact realVertexLimit_subset_roof_frontier C hL hupper

/-- Concrete closure field for the proper eventual-edge relation limit. -/
theorem eventualRelationBlueprint_vertices_closed
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := L.frontier) (closure := closedStage) I)
    (hclosed : Monotone closedStage)
    {a : Ladder.Stage theta}
    (hupper : ∀ i, (C.stage i).stageIndex ≤ a) :
    C.toIndexedRealExtensionChain.eventualRelationBlueprint.vertexSet ⊆
      closedStage a := by
  rw [C.toIndexedRealExtensionChain.eventualRelationBlueprint_vertexSet]
  exact realVertexLimit_subset_closedStage C hclosed hupper

/-- Concrete roof field for the final all-real relation limit. -/
theorem realRelationBlueprint_vertices_roofed
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := L.frontier) (closure := closedStage) I)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Ladder.Stage theta}
    (hupper : ∀ i, (C.stage i).stageIndex ≤ a) :
    C.toIndexedRealExtensionChain.realRelationBlueprint.vertexSet ⊆
      Gamma.roof (L.frontier a) := by
  rw [C.toIndexedRealExtensionChain.realRelationBlueprint_vertexSet]
  exact realVertexLimit_subset_roof_frontier C hL hupper

/-- Concrete closure field for the final all-real relation limit. -/
theorem realRelationBlueprint_vertices_closed
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := L.frontier) (closure := closedStage) I)
    (hclosed : Monotone closedStage)
    {a : Ladder.Stage theta}
    (hupper : ∀ i, (C.stage i).stageIndex ≤ a) :
    C.toIndexedRealExtensionChain.realRelationBlueprint.vertexSet ⊆
      closedStage a := by
  rw [C.toIndexedRealExtensionChain.realRelationBlueprint_vertexSet]
  exact realVertexLimit_subset_closedStage C hclosed hupper

#print axioms realVertexLimit_subset_roof_frontier
#print axioms realVertexLimit_subset_closedStage
#print axioms eventualRelationBlueprint_vertices_roofed
#print axioms realRelationBlueprint_vertices_closed

end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
