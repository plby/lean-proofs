/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RootReachablePathRetention
import ErdosProblems.Erdos599.Blueprint931
import ErdosProblems.Erdos599.HalfwayLinkageFirstBoundary

/-!
# Root-reachable realization in an arbitrary explicit web

The graph-independent form of the older root-reachable blueprint constructor.
No particular imaginary-edge predicate is used. Genuine roots and biuniqueness
suffice; unrooted components are discarded without losing any rooted old path.
-/

namespace Erdos599.RootReachableRelation

open Set DirectedPath Alternating Alternating.RelationDecomposition
open Blueprint.LinkageBlueprint

universe u

variable {V : Type u} (G : DWeb V) (E : Set (V × V)) (R : Set V)

theorem exists_warp_exact
    (hgraph : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hroots : ∀ x ∈ R, ¬ ∃ y, (y, x) ∈ E) :
    ∃ U : Set G.DPath, G.IsWarp U ∧
      familyEdges U = edges E R ∧ G.vertexSet U = carrier E R ∧
      G.initialSet U = R ∧
      G.terminalFrontier U = {x | x ∈ carrier E R ∧ ¬ ∃ y, (x, y) ∈ E} := by
  obtain ⟨O, hOE, hOC⟩ := Blueprint.exists_forwardOrientation_exact
    (edges E R) (carrier E R) ((edges_subset E R).trans hgraph)
    (fun _ he ↦ endpoints_mem E R he) (biUnique E R hbi)
    (no_directed_cycle E R hbi.1 hroots) (no_reverse_ray E R hbi.1 hroots)
  have hW : G.IsWarp O.rootPaths := O.rootPaths_pairwiseDisjoint
  have hE : familyEdges O.rootPaths = edges E R := O.rootPathEdges_eq.trans hOE
  have hV : G.vertexSet O.rootPaths = carrier E R :=
    (PathFilterComponents.ForwardOrientation.vertexSet_rootPaths G O).trans hOC
  refine ⟨O.rootPaths, hW, hE, hV, ?_, ?_⟩
  · rw [isWarp_initialSet_eq_noIncoming hW, hV, hE]
    ext x
    exact root_iff E R hroots
  · rw [isWarp_terminalFrontier_eq_noOutgoing hW, hV, hE]
    ext x
    constructor
    · rintro ⟨hx, hno⟩
      exact ⟨hx, fun hout ↦ hno ((hasOutgoing_iff E R hx).mpr hout)⟩
    · rintro ⟨hx, hno⟩
      exact ⟨hx, fun hout ↦ hno ((hasOutgoing_iff E R hx).mp hout)⟩

/-- Exact realization retaining all old vertices, edges and initials. -/
theorem exists_warp_extending (W : Set G.DPath)
    (hgraph : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hroots : ∀ x ∈ R, ¬ ∃ y, (y, x) ∈ E)
    (hold : familyEdges W ⊆ E) (hstart : G.initialSet W ⊆ R) :
    ∃ U : Set G.DPath, G.IsWarp U ∧
      familyEdges U = edges E R ∧ G.vertexSet U = carrier E R ∧
      G.initialSet U = R ∧
      G.terminalFrontier U = {x | x ∈ carrier E R ∧ ¬ ∃ y, (x, y) ∈ E} ∧
      G.vertexSet W ⊆ G.vertexSet U ∧ familyEdges W ⊆ familyEdges U ∧
      G.initialSet W ⊆ G.initialSet U := by
  obtain ⟨U, hU, hE, hV, hI, hT⟩ := exists_warp_exact G E R hgraph hbi hroots
  have hinit := hstart.trans (roots_subset_carrier E R)
  refine ⟨U, hU, hE, hV, hI, hT, ?_, ?_, ?_⟩
  · rw [hV]
    exact family_vertices_retained E R W hold hinit
  · rw [hE]
    exact family_edges_retained E R W hold hinit
  · rw [hI]
    exact hstart

#print axioms exists_warp_exact
#print axioms exists_warp_extending

end Erdos599.RootReachableRelation
