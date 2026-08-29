/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingReservedRelevantPruning
import ErdosProblems.Erdos599.DeferredGroundingSeparatorGeometry
import ErdosProblems.Erdos599.GroundingErasedForwardConflict
import ErdosProblems.Erdos599.GroundingSourceReachableSinkWarp
import ErdosProblems.Erdos599.HindranceGrounding

/-!
# The source-reachable warp of the final deferred stopped relation

This file fixes the actual final deferred controls and common stopping
frontier.  The locally bi-unique stopped relation is restricted to the
components reachable from the whole original source.  That restriction is
always a genuine warp, including its forward rays.

If every point of the common relevant frontier is source-reachable, the
frontier is a separating subset of the dynamic sink boundary.  The
source-reachable component warp is then a wave.  No compatibility or global
realization premise for the unreached part of the switched relation is used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.Alternating
open GroundingErasedDecode GroundingErasedForwardConflict
open GroundingSourceReachableSinkWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S
local notation "T" =>
  reservedStrongSelectedRelevantBB (L := L) (hL := hL) (S := S)

/-- The literal final deferred relation, stopped at the common frontier
which avoids both the reserved record and every selected starting record. -/
def reservedStrongSelectedSwitchedEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt U S K T

/-- The dynamic terminal frontier of the whole-source-reachable restriction
of the final stopped relation. -/
def reservedStrongSelectedReachableSinkBoundary : Set V :=
  sourceReachableSinkBoundary
    (reservedStrongSelectedSwitchedEdges
      (L := L) (hL := hL) (S := S)) Gamma.source

/-- Every common-frontier point which is reachable from an original source
is a literal dynamic sink. -/
theorem reservedStrongSelectedRelevantBB_subset_reachableSinkBoundary
    (hroot : ∀ t ∈ T, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ reservedStrongSelectedSwitchedEdges
          (L := L) (hL := hL) (S := S)) a t) :
    T ⊆ reservedStrongSelectedReachableSinkBoundary
      (L := L) (hL := hL) (S := S) := by
  intro t ht
  refine ⟨hroot t ht, ?_⟩
  exact boundary_noOutgoing_switchedAt U S K T ht

/-- Rooting the actual common relevant frontier makes the dynamic sink
boundary separating. -/
theorem reservedStrongSelectedReachableSinkBoundary_isSeparator_of_rooted
    (hroot : ∀ t ∈ T, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ reservedStrongSelectedSwitchedEdges
          (L := L) (hL := hL) (S := S)) a t) :
    Popular.IsSeparator Gamma
      (reservedStrongSelectedReachableSinkBoundary
        (L := L) (hL := hL) (S := S)) := by
  have hsubset :=
    reservedStrongSelectedRelevantBB_subset_reachableSinkBoundary
      (L := L) (hL := hL) (S := S) hroot
  intro p hpSource hpTarget
  obtain ⟨t, htp, htT⟩ :=
    reservedStrongSelectedRelevantBB_isSeparator
      (L := L) (hL := hL) (S := S) p hpSource hpTarget
  exact ⟨t, htp, hsubset htT⟩

/-- The whole-source-reachable part of the actual final stopped relation is
a genuine warp.  No acyclicity assertion is required for unreachable
components. -/
theorem exists_reservedStrongSelectedSourceReachableComponentWarp
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
        familyEdges W = RootReachableRelation.edges
          (reservedStrongSelectedSwitchedEdges
            (L := L) (hL := hL) (S := S)) Gamma.source ∧
        Gamma.vertexSet W = RootReachableRelation.carrier
          (reservedStrongSelectedSwitchedEdges
            (L := L) (hL := hL) (S := S)) Gamma.source ∧
        Gamma.initialSet W = Gamma.source ∧
        Gamma.terminalFrontier W =
          reservedStrongSelectedReachableSinkBoundary
            (L := L) (hL := hL) (S := S) := by
  apply GroundingSourceReachableSinkWarp.exists_sourceReachableComponentWarp
  · exact erasedSelectedSwitchedEdgesAt_subset_adj U S K T
  · exact erasedSelectedSwitchedEdgesAt_biUnique U S K T
      (popularAuxiliary_proxyPathsFaithful L hL)
  · intro x hx
    rintro ⟨y, hyx⟩
    exact hNoEnter
      (erasedSelectedSwitchedEdgesAt_subset_adj U S K T hyx) hx

/-- Positive global branch: full rooting of the actual common frontier
produces a ray-compatible wave whose terminal frontier is precisely the
dynamic reachable-sink boundary. -/
theorem exists_reservedStrongSelectedSourceReachableWave_of_rooted
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hroot : ∀ t ∈ T, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ reservedStrongSelectedSwitchedEdges
          (L := L) (hL := hL) (S := S)) a t) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWave W ∧
        Gamma.IsWarp W ∧
        familyEdges W = RootReachableRelation.edges
          (reservedStrongSelectedSwitchedEdges
            (L := L) (hL := hL) (S := S)) Gamma.source ∧
        Gamma.vertexSet W = RootReachableRelation.carrier
          (reservedStrongSelectedSwitchedEdges
            (L := L) (hL := hL) (S := S)) Gamma.source ∧
        Gamma.initialSet W = Gamma.source ∧
        Gamma.terminalFrontier W =
          reservedStrongSelectedReachableSinkBoundary
            (L := L) (hL := hL) (S := S) := by
  obtain ⟨W, hW, hWedges, hWvertex, hWinitial, hWterminal⟩ :=
    exists_reservedStrongSelectedSourceReachableComponentWarp
      (L := L) (hL := hL) (S := S) hNoEnter
  refine ⟨W, ?_, hW, hWedges, hWvertex, hWinitial, hWterminal⟩
  apply isWave_of_terminalFrontier_isSeparator hW
  · rw [hWinitial]
  · rw [hWterminal]
    exact reservedStrongSelectedReachableSinkBoundary_isSeparator_of_rooted
      (L := L) (hL := hL) (S := S) hroot

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.exists_reservedStrongSelectedSourceReachableComponentWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.exists_reservedStrongSelectedSourceReachableWave_of_rooted

