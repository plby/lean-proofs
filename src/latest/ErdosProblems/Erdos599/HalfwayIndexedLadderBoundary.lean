/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayIndexedLadderLimitRoof
import ErdosProblems.Erdos599.IndexedRelationLimitGeometry

/-!
# Actual target and stability geometry of ladder limits

A target vertex never belongs to a strict roof: its trivial target path
makes it essential whenever it is roofed.  Thus every target vertex of an
indexed carrier belongs to the global persistent frontier.  Strict frontier
chronology also supplies the precise old-roof/new-frontier intersection
used by the indexed proper-limit stability proof.
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

variable {V : Type u} {I : Type v} [LinearOrder I] [Nonempty I]
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}
variable {L : Gamma.KappaLadder theta}
variable {closedStage : Ladder.Stage theta → Set V}

private theorem target_mem_boundary_of_mem_roof
    {S : Set V} {x : V} (hxB : x ∈ Gamma.target)
    (hxRoof : x ∈ Gamma.roof S) : x ∈ S := by
  let p := DirectedPath.FinitePath.trivial Gamma.graph x
  obtain ⟨y, hyp, hyS⟩ := hxRoof p ⟨rfl, hxB⟩
  have hyx : y = x := by simpa [p] using hyp
  exact hyx ▸ hyS

/-- No target vertex can lie in the strict roof of any set. -/
theorem target_not_mem_strictRoof
    {S : Set V} {x : V} (hxB : x ∈ Gamma.target) :
    x ∉ Gamma.strictRoof S := by
  rintro ⟨hxRoof, hxNotEssential⟩
  exact hxNotEssential <| CardinalInduction.target_mem_essential hxB
    (target_mem_boundary_of_mem_roof hxB hxRoof)

/-- The carrier-local target hypothesis for indexed limits is a theorem
for the actual persistent set, without normalization or extra choices. -/
theorem target_inter_realVertexLimit_subset_persistent
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := L.limitRoof \ L.limitStrictRoof) (B := Gamma.target)
      (slice := L.frontier) (closure := closedStage) I) :
    Gamma.target ∩ C.toIndexedRealExtensionChain.realVertexLimit ⊆
      L.limitRoof \ L.limitStrictRoof := by
  rintro x ⟨hxB, hxLimit⟩
  change x ∈ ⋃ i, (C.stage i).blueprint.realPart.vertices at hxLimit
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxLimit
  refine ⟨?_, ?_⟩
  · exact Set.mem_iUnion.2 ⟨(C.stage i).stageIndex,
      (C.stage i).isBlueprint.vertices_roofed hxi⟩
  · intro hxStrict
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.1 hxStrict
    exact target_not_mem_strictRoof hxB hxa

/-- The part of a later frontier inside an old roof is on the old
frontier itself. Only strict chronology and the essential-subset fact
are needed, not an equality of the two frontiers. -/
theorem oldRoof_inter_laterFrontier_subset
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a b : Ladder.Stage theta} (hab : a ≤ b) :
    Gamma.roof (L.frontier a) ∩ L.frontier b ⊆ L.frontier a := by
  rcases hab.lt_or_eq with hab | rfl
  · rintro x ⟨hxRoof, hxb⟩
    by_contra hxa
    have hxStrict : x ∈ Gamma.strictRoof (L.frontier a) :=
      ⟨hxRoof, fun hxEssential ↦ hxa (Gamma.essential_subset _ hxEssential)⟩
    exact Set.disjoint_left.1 (hL.strictFrontierChronology hab) hxStrict hxb
  · exact Set.inter_subset_right

/-- Genuine proper-limit stability at any upper-bound ladder frontier.
The index need not be artificially identified with an earlier stage. -/
theorem eventualRelationBlueprint_stable_at_upper
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := L.limitRoof \ L.limitStrictRoof) (B := Gamma.target)
      (slice := L.frontier) (closure := closedStage) I)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Ladder.Stage theta}
    (hupper : ∀ i, (C.stage i).stageIndex ≤ a) :
    C.toIndexedRealExtensionChain.eventualRelationBlueprint.Stable
      (L.frontier a) (L.limitRoof \ L.limitStrictRoof) := by
  exact C.toIndexedRealExtensionChain.eventualRelationBlueprint_stable
    (fun i ↦ L.frontier (C.stage i).stageIndex)
    (fun i ↦ closedStage (C.stage i).stageIndex) (L.frontier a)
    (fun i ↦ (C.stage i).isBlueprint) (fun i ↦ (C.stage i).stable)
    (fun i ↦ oldRoof_inter_laterFrontier_subset hL (hupper i))
    (target_inter_realVertexLimit_subset_persistent C)

#print axioms target_inter_realVertexLimit_subset_persistent
#print axioms oldRoof_inter_laterFrontier_subset
#print axioms eventualRelationBlueprint_stable_at_upper

end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
