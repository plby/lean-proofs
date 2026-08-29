/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RootReachablePathRetention
import ErdosProblems.Erdos599.GlobalBlueprintReplacement

/-!
# Actual path-family realization of root-reachable relation components

The starting relation needs only local bi-uniqueness and genuine roots.
Unrooted cycles and reverse rays are discarded by the proved reachable
restriction, while every old path rooted in the chosen roots is retained.
Source/sink geometry and the strong-edge property remain independent.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating Alternating.RelationDecomposition

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The reachable part has an actual warp realization with exact edges,
carrier, roots and sinks. No global cycle or reverse-ray premise is used. -/
theorem exists_rootReachableBlueprint
    (E : Set (V × V)) (R : Set V)
    (hgraph : E ⊆ {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hroots : ∀ x ∈ R, ¬ ∃ y, (y, x) ∈ E) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      U.edgeSet = RootReachableRelation.edges E R ∧
      U.vertexSet = RootReachableRelation.carrier E R ∧
      U.initialSet = R ∧
      U.terminalSet = {x | x ∈ RootReachableRelation.carrier E R ∧
        ¬ ∃ y, (x, y) ∈ E} := by
  obtain ⟨O, hOE, hOC⟩ := exists_forwardOrientation_exact
    (RootReachableRelation.edges E R) (RootReachableRelation.carrier E R)
    ((RootReachableRelation.edges_subset E R).trans hgraph)
    (fun _ he => RootReachableRelation.endpoints_mem E R he)
    (RootReachableRelation.biUnique E R hbi)
    (RootReachableRelation.no_directed_cycle E R hbi.1 hroots)
    (RootReachableRelation.no_reverse_ray E R hbi.1 hroots)
  refine ⟨orientationBlueprint O, ?_, ?_, ?_, ?_⟩
  · rw [orientationBlueprint_edgeSet, hOE]
  · rw [orientationBlueprint_vertexSet, hOC]
  · rw [orientationBlueprint_initialSet_eq_no_incoming, hOC, hOE]
    ext x
    exact RootReachableRelation.root_iff E R hroots
  · rw [orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
    ext x
    constructor
    · rintro ⟨hx, hno⟩
      exact ⟨hx, fun hout => hno
        ((RootReachableRelation.hasOutgoing_iff E R hx).mpr hout)⟩
    · rintro ⟨hx, hno⟩
      exact ⟨hx, fun hout => hno
        ((RootReachableRelation.hasOutgoing_iff E R hx).mp hout)⟩

/-- All current paths, including rays and singleton paths, survive provided
their initial vertices are genuine roots of the new relation. -/
theorem exists_rootReachableBlueprint_extending
    (current : LinkageBlueprint Gamma Y kappa)
    (E : Set (V × V)) (R : Set V)
    (hgraph : E ⊆ {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hroots : ∀ x ∈ R, ¬ ∃ y, (y, x) ∈ E)
    (hold : current.edgeSet ⊆ E)
    (hstart : current.initialSet ⊆ R) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      current.OrdinaryExtends U ∧
      U.edgeSet = RootReachableRelation.edges E R ∧
      U.vertexSet = RootReachableRelation.carrier E R ∧
      U.initialSet = R ∧
      U.terminalSet = {x | x ∈ RootReachableRelation.carrier E R ∧
        ¬ ∃ y, (x, y) ∈ E} := by
  obtain ⟨U, hUE, hUC, hUR, hUT⟩ :=
    exists_rootReachableBlueprint E R hgraph hbi hroots
  have hinit : (imaginaryWeb Gamma Y kappa).initialSet current.paths ⊆
      RootReachableRelation.carrier E R :=
    hstart.trans (RootReachableRelation.roots_subset_carrier E R)
  have hvertices := RootReachableRelation.family_vertices_retained
    (Gamma := imaginaryWeb Gamma Y kappa) E R current.paths hold hinit
  have hedges := RootReachableRelation.family_edges_retained
    (Gamma := imaginaryWeb Gamma Y kappa) E R current.paths hold hinit
  refine ⟨U, ?_, hUE, hUC, hUR, hUT⟩
  constructor
  · change current.vertexSet ⊆ U.vertexSet
    rw [hUC]
    exact hvertices
  · change current.edgeSet ⊆ U.edgeSet
    rw [hUE]
    exact hedges

#print axioms exists_rootReachableBlueprint
#print axioms exists_rootReachableBlueprint_extending

end Erdos599.Blueprint.LinkageBlueprint
