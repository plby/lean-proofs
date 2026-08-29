/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GlobalBlueprintReplacement

/-!
# Exact edge and carrier equations for a whole-family replacement

The final scheduler takes unions of the concrete splice relations.  It
therefore needs the equations identifying the orientation used by the result
blueprint with the input splice relation.  The original existence theorem
uses these equations internally and then forgets them; this exact variant
retains them.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Construct the oriented replacement while retaining the exact edge and
carrier equations of the orientation. -/
theorem WholeFamilySpliceRelation.exists_orientedReplacement_exact
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (S : WholeFamilySpliceRelation W A u T Z persistent B) :
    exists R : WholeFamilyOrientedReplacement W A u T Z persistent B,
      R.orientation.edge = S.edge /\
        R.orientation.carrier = S.carrier := by
  obtain ⟨O, hOE, hOC⟩ := exists_forwardOrientation_exact
    S.edge S.carrier S.edge_in_graph S.endpoints_mem S.biunique
      S.no_directed_cycle S.no_reverse_ray
  let R : WholeFamilyOrientedReplacement W A u T Z persistent B := {
    orientation := O
    assigned_edges := by
      rw [hOE]
      exact S.assigned_edges
    infinite_sources_terminal := by
      intro x hx
      rw [orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
      exact S.infinite_sources_sink hx
    terminal_boundary := by
      rw [orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
      exact S.sink_boundary
    vertices_roofed := by
      rw [orientationBlueprint_vertexSet, hOC]
      exact S.vertices_roofed
    covers_source := by
      rw [orientationBlueprint_initialSet_eq_no_incoming,
        retainedReferenceInitials, orientationBlueprint_vertexSet, hOC, hOE]
      exact S.covers_source
    vertices_closed := by
      rw [orientationBlueprint_vertexSet, hOC]
      exact S.vertices_closed
    card_paths := by
      change #(Set.range O.rootPath) ≤ kappa
      refine Cardinal.mk_range_le.trans ?_
      refine (Cardinal.mk_subtype_mono (fun x hx => hx.1)).trans ?_
      simpa only [hOC] using S.card_carrier
    infinitely_many_strong := by
      intro r hr
      apply S.every_relation_ray_strong r
      intro e he
      rw [← hOE, ← orientationBlueprint_edgeSet O]
      exact Set.mem_iUnion.2 ⟨(Sum.inr r :
        DirectedPath.Path (imaginaryGraph Gamma Y kappa)),
          Set.mem_iUnion.2 ⟨hr, he⟩⟩
    stable_boundary := by
      rw [orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
      exact S.stable_boundary
    real_part_extends := by
      constructor
      · simpa only [realPart_vertices, orientationBlueprint_vertexSet, hOC]
          using S.old_real_vertices
      · simpa only [realPart_edges, orientationBlueprint_edgeSet, hOE,
          relationRealEdges] using S.old_real_edges
    old_vertices_accounted := by
      intro x hx
      rcases S.old_vertices_accounted hx with
        (hterminal | hcommon) | hcompleted
      · apply Or.inl
        apply Or.inl
        refine ⟨?_, hterminal.2⟩
        rw [orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
        exact hterminal.1
      · apply Or.inl
        apply Or.inr
        rcases hcommon with ⟨y, hyW, hyS⟩
        refine ⟨y, hyW, ?_⟩
        change (x, y) ∈ (orientationBlueprint O).edgeSet
        rw [orientationBlueprint_edgeSet, hOE]
        exact hyS
      · apply Or.inr
        rcases hcompleted with ⟨p, hpB, hpvertex, hpedge, hxp⟩
        refine ⟨p, hpB, ?_, ?_, hxp⟩
        · simpa only [realPart_vertices, orientationBlueprint_vertexSet, hOC]
            using hpvertex
        · simpa only [realPart_edges, orientationBlueprint_edgeSet, hOE,
            relationRealEdges] using hpedge
    target_path := S.target_path
    target_path_start := S.target_path_start
    target_path_finish := S.target_path_finish
    target_path_vertices := by
      simpa only [realPart_vertices, orientationBlueprint_vertexSet, hOC]
        using S.target_path_vertices
    target_path_edges := by
      simpa only [realPart_edges, orientationBlueprint_edgeSet, hOE,
        relationRealEdges] using S.target_path_edges
    preserves_other_real_terminals := by
      simpa only [FamilyGraph.terminals, FamilyGraph.tails, realPart_vertices,
        realPart_edges, orientationBlueprint_vertexSet,
        orientationBlueprint_edgeSet, hOC, hOE, relationRealTerminals,
        relationRealEdges] using S.preserves_other_real_terminals }
  exact ⟨R, hOE, hOC⟩

end LinkageBlueprint
end Blueprint
end Erdos599

