/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMarkerAbsorbedMacroRequest

/-!
# Accounting for the marker-absorbed macro stage

The marker-absorbed request constructs the exact local relation used in
Assertion 9.31: the canonical inside part of the honest later row, together
with one compressed edge for every finite outside assignment.  The macro
survivor lemmas already prove attachment, bi-uniqueness, rank, source
coverage, and the absence of a forward ray.

This file supplies the remaining translation from the concrete continuation
data to `ClubStageUnionData`.  The input below is deliberately phrased in
terms of the honest later row, the old blueprint, and actual finite paths.
In particular it does not assume any conclusion about a subsequently chosen
orientation or result blueprint.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating
open CardinalInduction

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

namespace MarkerAbsorbedMacroRequest

variable {S : MarkerAbsorbedMacroSeed
  (Gamma := Gamma) (Y := Y) (kappa := kappa)}

/-- The exact inside-plus-macro relation carried by a marker-absorbed
request. -/
def macroEdge (R : MarkerAbsorbedMacroRequest S) : Set (V × V) :=
  R.inside.insideFamily.edgeSet ∪
    assignedFiniteEdges
      (Zf := FracturedWarp.ofWarp
        (outsideReference S.later R.closureSet)
        (outsideReference_isWarp S.later_isWarp))
      R.assignment.assignment

/-- A later-row vertex already swallowed by the closure belongs to the
canonical inside carrier. -/
theorem mem_insideCarrier_of_mem_later_of_mem_closure
    (R : MarkerAbsorbedMacroRequest S) {x : V}
    (hxrow : x ∈ Gamma.vertexSet S.later)
    (hxclosed : x ∈ R.closureSet) :
    x ∈ R.inside.insideFamily.vertexSet := by
  rw [R.inside.vertexSet_eq]
  exact Or.inl (Or.inl ⟨hxrow, hxclosed⟩)

/-- A literal later-row edge whose endpoints were swallowed by the closure
is an inside edge of the macro relation. -/
theorem rowEdge_mem_macroEdge_of_endpoints_mem_closure
    (R : MarkerAbsorbedMacroRequest S) {x y : V}
    (hxy : (x, y) ∈ familyEdges S.later)
    (hx : x ∈ R.closureSet) (hy : y ∈ R.closureSet) :
    (x, y) ∈ R.macroEdge := by
  apply Or.inl
  rw [R.inside.edgeSet_eq]
  exact ⟨hxy, hx, hy⟩

/-- The canonical carrier consists of closed vertices and the two uncovered
cut boundaries.  The latter lie in the stored `before` set by the exact
row endpoint hypotheses of `MarkerAbsorbedMacroSeed`. -/
theorem insideCarrier_subset_closure_union_before
    (R : MarkerAbsorbedMacroRequest S) :
    R.inside.insideFamily.vertexSet ⊆ R.closureSet ∪ S.before := by
  intro x hx
  rw [R.inside.vertexSet_eq] at hx
  rcases hx with (hxbase | hxinitial) | hxterminal
  · exact Or.inl hxbase.2
  · apply Or.inr
    apply (S.source_location ?_).1
    refine ⟨?_, hxinitial.2⟩
    apply initialSet_outsideReference_subset
    rw [← cutInitial_eq_initialSet_outsideReference
      S.later_isWarp S.later_finite R.later_closed]
    exact hxinitial.1
  · apply Or.inr
    apply (S.terminal_location ?_).1
    refine ⟨?_, hxterminal.2⟩
    apply terminalFrontier_outsideReference_subset
    rw [← cutTerminal_eq_terminalFrontier_outsideReference
      S.later_isWarp S.later_finite R.later_closed]
    exact hxterminal.1

/-- The sharper roof form of the carrier bound: the two uncovered boundary
parts use the roof coordinates stored in the seed itself. -/
theorem insideCarrier_subset_outerRoof
    (R : MarkerAbsorbedMacroRequest S)
    (hinner : S.innerRoof ⊆ S.outerRoof) :
    R.inside.insideFamily.vertexSet ⊆ S.outerRoof := by
  intro x hx
  rw [R.inside.vertexSet_eq] at hx
  rcases hx with (hxbase | hxinitial) | hxterminal
  · exact R.contained_in_roof hxbase.2
  · have hloc := S.source_location ⟨
      initialSet_outsideReference_subset (by
        rw [← cutInitial_eq_initialSet_outsideReference
          S.later_isWarp S.later_finite R.later_closed]
        exact hxinitial.1), hxinitial.2⟩
    exact hinner hloc.2
  · exact (S.terminal_location ⟨
      terminalFrontier_outsideReference_subset (by
        rw [← cutTerminal_eq_terminalFrontier_outsideReference
          S.later_isWarp S.later_finite R.later_closed]
        exact hxterminal.1), hxterminal.2⟩).2

/-- The canonical inside carrier has the required stage cardinality. -/
theorem mk_insideCarrier_le
    (R : MarkerAbsorbedMacroRequest S) :
    #R.inside.insideFamily.vertexSet ≤ kappa := by
  refine (Cardinal.mk_subtype_mono
    R.insideCarrier_subset_closure_union_before).trans ?_
  exact (Cardinal.mk_union_le R.closureSet S.before).trans
    (Cardinal.add_le_of_le S.kappa_infinite R.closure_card S.before_card)

/-- A terminal of the honest later row has no outgoing edge in the complete
macro relation.  For a compressed edge, its source and target are the
initial and terminal of the same row member; row terminality and the
nontriviality certificate rule this out. -/
theorem no_macroEdge_out_of_rowTerminal
    (R : MarkerAbsorbedMacroRequest S)
    (hnontrivial : CanonicalInsideCut.AssignedRowPathsNontrivial
      R.assignment)
    {x : V} (hx : x ∈ Gamma.terminalFrontier S.later) :
    ¬ ∃ y, (x, y) ∈ R.macroEdge := by
  rintro ⟨y, hxy⟩
  rcases hxy with hxy | hxy
  · have hx' := hx
    rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing
      S.later_isWarp S.later_finite] at hx'
    apply hx'.2
    exact ⟨y, by
      rw [R.inside.edgeSet_eq] at hxy
      exact hxy.1⟩
  · obtain ⟨s, hterm, hsx⟩ := hxy
    have hpterm := R.assignment.assigned_terminal_initialPath
      S.later_isWarp R.outside_subset s hterm
    let p : outsideReference S.later R.closureSet :=
      initialPath (outsideReference S.later R.closureSet)
        ⟨s.1, s.property.1⟩
    have hpinitial : p.1.initial = s.1 := initialPath_initial _ _
    have hxinitial : p.1.initial = x := hpinitial.trans hsx
    obtain ⟨q, hqrow, hqterminal⟩ := hx
    have hxp : x ∈ p.1.support :=
      hxinitial ▸ p.1.initial_mem_support
    have hxq : x ∈ q.support := Gamma.terminal_mem_support hqterminal
    have hpq : p.1 = q :=
      DWeb.IsWarp.eq_of_mem_support S.later_isWarp p.2.1 hqrow hxp hxq
    have hxyEq : x = y := by
      have hsame : Gamma.terminal? p.1 = some x :=
        (congrArg Gamma.terminal? hpq).trans hqterminal
      exact Option.some.inj (hsame.symm.trans hpterm)
    exact hnontrivial s y hterm (hsx.trans hxyEq)

/-- Every full blueprint terminal is also a terminal of its real part. -/
theorem terminalSet_subset_realPart_terminals
    (old : LinkageBlueprint Gamma Y kappa) :
    old.terminalSet ⊆ old.realPart.terminals := by
  intro x hx
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp, hpterm⟩ := hx
    exact ⟨p, hp, (imaginaryWeb Gamma Y kappa).terminal_mem_support hpterm⟩
  · rintro ⟨y, hy⟩
    exact old.no_outgoing_of_mem_terminalSet hx
      ⟨y, old.realPart_edges_subset hy⟩

/-- Concrete continuation and accounting data for one marker-absorbed
stage.  Every field is stated before orientation, using the old blueprint,
the honest later row, the closure, and actual original-graph paths.

`old_nonterminal_common` is the pathwise form of the middle alternative of
(9.32).  Full old terminals other than the scheduled `u` are retained as
later-row terminals; the scheduled terminal is accounted for by
`targetPath`. -/
structure MacroStageContinuationData
    (C : ClubStageGeometry Gamma Y kappa theta)
    (old : LinkageBlueprint Gamma Y kappa) (u : V)
    (R : MarkerAbsorbedMacroRequest S) where
  before_eq : S.before = C.before
  innerRoof_eq : S.innerRoof = C.innerRoof
  outerRoof_eq : S.outerRoof = C.outerRoof
  closure_subset_closedSet : R.closureSet ⊆ C.closedSet
  later_linkage : IsLinkageBetween Gamma Gamma.source C.newSlice S.later
  later_terminals_persistent :
    Gamma.terminalFrontier S.later ⊆ C.persistent
  old_vertices_row : old.vertexSet ⊆ Gamma.vertexSet S.later
  old_vertices_closure : old.vertexSet ⊆ R.closureSet
  old_real_edges_row : old.realPart.edges ⊆ familyEdges S.later
  old_nonterminal_common : ∀ x ∈ old.vertexSet,
    x ∉ old.terminalSet →
      ∃ y, (x, y) ∈ old.familyGraph.edges ∩ familyEdges S.later
  targetPath : FinitePath Gamma.graph
  targetPath_start : targetPath.start = u
  targetPath_finish : targetPath.finish ∈ Gamma.target
  targetPath_vertices_row : targetPath.support ⊆ Gamma.vertexSet S.later
  targetPath_vertices_closure : targetPath.support ⊆ R.closureSet
  targetPath_edges_row : targetPath.edgeSet ⊆ familyEdges S.later
  preserves_other_row_terminals :
    old.realPart.terminals \ {u} ⊆ Gamma.terminalFrontier S.later

namespace MacroStageContinuationData

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {old : LinkageBlueprint Gamma Y kappa} {u : V}
variable {R : MarkerAbsorbedMacroRequest S}

variable (D : MacroStageContinuationData C old u R)

include D

/-- Endpoint purity of the honest later linkage supplies the nontriviality
needed by the common later-row rank. -/
theorem assignedRowPathsNontrivial :
    CanonicalInsideCut.AssignedRowPathsNontrivial R.assignment := by
  apply CanonicalInsideCut.assignedRowPathsNontrivial_of_clubStage
    C R.assignment
  · simpa only [← D.before_eq, ← D.innerRoof_eq] using S.source_location
  · exact D.later_linkage.terminalFrontier_subset

/-- Old real vertices are swallowed by the canonical inside carrier. -/
theorem old_real_vertices :
    old.realPart.vertices ⊆ R.inside.insideFamily.vertexSet := by
  exact R.inside.oldRealVertices_subset old D.old_vertices_row
    D.old_vertices_closure

/-- Every old real edge survives literally as an inside real edge. -/
theorem old_real_edges : old.realPart.edges ⊆
    relationRealEdges (Gamma := Gamma) R.macroEdge := by
  intro e he
  have hend := edgeSet_endpoints_mem_vertexSet old
    (old.realPart_edges_subset he)
  exact ⟨R.rowEdge_mem_macroEdge_of_endpoints_mem_closure
      (D.old_real_edges_row he)
      (D.old_vertices_closure hend.1)
      (D.old_vertices_closure hend.2),
    old.realPart_edges_are_original he⟩

/-- The scheduled target route survives literally in the macro relation. -/
theorem targetPath_vertices :
    D.targetPath.support ⊆ R.inside.insideFamily.vertexSet := by
  exact R.inside.targetPath_support_subset D.targetPath
    D.targetPath_vertices_row D.targetPath_vertices_closure

theorem targetPath_edges : D.targetPath.edgeSet ⊆
    relationRealEdges (Gamma := Gamma) R.macroEdge := by
  intro e he
  have hend := D.targetPath.edgeSet_subset_support_prod he
  exact ⟨R.rowEdge_mem_macroEdge_of_endpoints_mem_closure
      (D.targetPath_edges_row he)
      (D.targetPath_vertices_closure hend.1)
      (D.targetPath_vertices_closure hend.2),
    D.targetPath.edgeSet_subset_adj he⟩

/-- Every non-scheduled old real terminal remains a real terminal of the
macro relation. -/
theorem preserves_other_real_terminals :
    old.realPart.terminals \ {u} ⊆
      relationRealTerminals (Gamma := Gamma) R.macroEdge
        R.inside.insideFamily.vertexSet := by
  intro x hx
  refine ⟨D.old_real_vertices hx.1.1, ?_⟩
  rintro ⟨y, hy⟩
  exact R.no_macroEdge_out_of_rowTerminal D.assignedRowPathsNontrivial
    (D.preserves_other_row_terminals hx) ⟨y, hy.1⟩

/-- Definition (9.32) follows from the explicit old continuation data.
Nonterminals use their common old/later outgoing edge.  An old terminal
different from `u` remains a sink, while `u` lies on the stored completed
target route. -/
theorem old_vertices_accounted : old.vertexSet ⊆
    ({x | x ∈ R.inside.insideFamily.vertexSet ∧
      ¬ ∃ y, (x, y) ∈ R.macroEdge} ∩ old.terminalSet) ∪
      {x | ∃ y,
        (x, y) ∈ old.familyGraph.edges ∩ R.macroEdge} ∪
        relationCompletedRealVertices (Gamma := Gamma) R.macroEdge
          R.inside.insideFamily.vertexSet Gamma.target := by
  intro x hxold
  by_cases hxterminal : x ∈ old.terminalSet
  · by_cases hxu : x = u
    · subst x
      apply Or.inr
      refine ⟨D.targetPath, D.targetPath_finish,
        D.targetPath_vertices, D.targetPath_edges, ?_⟩
      simpa only [D.targetPath_start] using D.targetPath.start_mem_support
    · apply Or.inl
      apply Or.inl
      refine ⟨⟨D.old_real_vertices
          (terminalSet_subset_realPart_terminals old hxterminal).1, ?_⟩,
        hxterminal⟩
      exact R.no_macroEdge_out_of_rowTerminal D.assignedRowPathsNontrivial
        (D.preserves_other_row_terminals ⟨
          terminalSet_subset_realPart_terminals old hxterminal,
          by simpa only [Set.mem_singleton_iff]⟩)
  · apply Or.inl
    apply Or.inr
    obtain ⟨y, hyold, hyrow⟩ := D.old_nonterminal_common x hxold hxterminal
    refine ⟨y, hyold, ?_⟩
    have hend := edgeSet_endpoints_mem_vertexSet old hyold
    exact R.rowEdge_mem_macroEdge_of_endpoints_mem_closure hyrow
      (D.old_vertices_closure hend.1)
      (D.old_vertices_closure hend.2)

/-- The later frontier is persistent, hence every macro sink on the new
slice is persistent. -/
theorem stable_boundary :
    {x | x ∈ R.inside.insideFamily.vertexSet ∧
      ¬ ∃ y, (x, y) ∈ R.macroEdge} ∩ C.newSlice ⊆
        C.persistent := by
  intro x hx
  exact R.inside.macroFullSinkBoundary R.assignment S.later_isWarp
    S.later_finite R.reference_closed R.outside_subset R.later_closed
      D.later_terminals_persistent hx.1

/-- The complete concrete `ClubStageUnionData` generated by the
marker-absorbed macro request and its source-level continuation data. -/
noncomputable def toClubStageUnionData :
    ClubStageUnionData C old
      (Zf := FracturedWarp.ofWarp
        (outsideReference S.later R.closureSet)
        (outsideReference_isWarp S.later_isWarp))
      R.assignment.assignment u where
  inside := R.inside.insideFamily.edgeSet
  carrier := R.inside.insideFamily.vertexSet
  inside_in_graph := by
    intro e he
    rw [R.inside.edgeSet_eq] at he
    exact original_adj_imaginaryGraph
      (insideFamilyEdges_in_graph S.later R.closureSet he)
  inside_endpoints := fun e he ↦
    edgeSet_endpoints_mem_vertexSet R.inside.insideFamily he
  assigned_endpoints := by
    intro e he
    obtain ⟨s, hterm, hs⟩ := he
    have hsource := R.inside.macroAssignmentSource_mem_terminalSet
      S.later_isWarp S.later_finite R.later_closed s
    have htarget := R.inside.macroAssignmentTarget_mem_initialSet
      R.assignment S.later_isWarp S.later_finite R.later_closed s hterm
    rw [R.inside.insideFamily.terminalSet_eq_no_outgoing] at hsource
    rw [R.inside.insideFamily.initialSet_eq_no_incoming] at htarget
    exact ⟨hs ▸ hsource.1, htarget.1⟩
  inside_biunique := by
    change Relator.BiUnique (fun x y ↦
      (x, y) ∈ familyEdges
        (Γ := imaginaryWeb Gamma Y kappa) R.inside.insideFamily.paths)
    exact Alternating.IsWarp.familyEdges_biUnique R.inside.insideFamily.isWarp
  cross_in := by
    intro x y z hxz hyz
    exact (R.inside.macroFullRelation_biUnique R.assignment
      S.later_isWarp S.later_finite R.later_closed).1
        (Or.inl hxz) (Or.inr hyz)
  cross_out := by
    intro x y z hxy hxz
    exact (R.inside.macroFullRelation_biUnique R.assignment
      S.later_isWarp S.later_finite R.later_closed).2
        (Or.inl hxy) (Or.inr hxz)
  rank := laterRowRank S.later S.later_isWarp
  inside_rank := fun hxy ↦
    R.inside.inside_rank_laterRowRank S.later_isWarp hxy
  assigned_rank := fun hxy ↦
    CanonicalInsideCut.assigned_rank_laterRowRank R.assignment
      S.later_isWarp S.later_finite R.outside_subset
        D.assignedRowPathsNontrivial hxy
  infinite_sources_sink := by
    rintro x ⟨s, hsx, hinfinite⟩
    exact False.elim
      (R.assignment.assigned_not_infinite S.later_isWarp
        R.reference_closed R.outside_subset s hinfinite)
  sink_boundary := by
    intro x hx
    exact Or.inr (R.inside.macroFullSinkBoundary R.assignment
      S.later_isWarp S.later_finite R.reference_closed R.outside_subset
        R.later_closed D.later_linkage.terminalFrontier_subset hx)
  carrier_roofed := by
    have hinner : S.innerRoof ⊆ S.outerRoof := by
      intro x hx
      rw [D.innerRoof_eq] at hx
      rw [D.outerRoof_eq]
      exact Gamma.strictRoof_subset_roof C.newSlice hx
    simpa only [← D.outerRoof_eq] using
      (R.insideCarrier_subset_outerRoof hinner)
  covers_source := by
    intro x hxsource
    rcases R.inside.macroCoversSource S.later_isWarp S.later_finite
        R.later_closed R.reference_closed R.outside_subset
          D.later_linkage.initialSet_eq
          D.later_linkage.terminalFrontier_subset hxsource with
      hxinitial | hxreference
    · apply Or.inl
      have hnoassigned :=
        R.inside.macroCoveredInitial_not_assignedTarget R.assignment
          S.later_isWarp R.outside_subset D.later_linkage.initialSet_eq
            D.assignedRowPathsNontrivial ⟨hxsource, hxinitial⟩
      have hnoinside :=
        R.inside.insideFamily.no_incoming_of_mem_initialSet hxinitial
      rw [R.inside.insideFamily.initialSet_eq_no_incoming] at hxinitial
      refine ⟨hxinitial.1, ?_⟩
      rintro ⟨y, hy | hy⟩
      · exact hnoinside ⟨y, hy⟩
      · exact hnoassigned ⟨y, hy⟩
    · exact Or.inr hxreference
  carrier_closed := by
    intro x hx
    rcases R.insideCarrier_subset_closure_union_before hx with hx | hx
    · exact D.closure_subset_closedSet hx
    · apply C.before_subset_closedSet
      simpa only [← D.before_eq] using hx
  card_carrier := R.mk_insideCarrier_le
  every_relation_ray_strong :=
    R.inside.macroEveryRelationRayStrong R.assignment
      S.later_isWarp S.later_finite R.outside_subset
  stable_boundary := D.stable_boundary
  old_real_vertices := D.old_real_vertices
  old_real_edges := D.old_real_edges
  old_vertices_accounted := D.old_vertices_accounted
  target_path := D.targetPath
  target_path_start := D.targetPath_start
  target_path_finish := D.targetPath_finish
  target_path_vertices := D.targetPath_vertices
  target_path_edges := D.targetPath_edges
  preserves_other_real_terminals := D.preserves_other_real_terminals

end MacroStageContinuationData
end MarkerAbsorbedMacroRequest

end LinkageBlueprint
end Blueprint
end Erdos599
