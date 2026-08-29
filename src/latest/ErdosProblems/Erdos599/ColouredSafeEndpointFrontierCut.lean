/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointBlueprintReplacements
import ErdosProblems.Erdos599.ColouredSafeEdgeCut

/-!
# Exposing a frontier tail by cutting its nonreal edge

Endpoint pruning does not imply that imaginary-edge endpoints avoid the
frontier. Cutting a nonreal outgoing edge at such a tail preserves all
real edges and vertices and makes the tail an actual full terminal.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {a : Stage (succ kappa)}
variable {W : Set (web C).DPath}

theorem IsBlueprint.exists_frontierCut (hW : IsBlueprint C a W)
    {s t : V} (hedge : (s, t) ∈ familyEdges W) (hne : s ≠ t)
    (hn : ¬Gamma.graph.Adj s t) (hs : s ∈ C.ladder.frontier a) :
    ∃ U : Set (web C).DPath, IsBlueprint C a U ∧
      RealAdvance Gamma (web C) W U (C.ladder.frontier a) ∧
      s ∈ (web C).terminalFrontier U ∧ RealReach Gamma (web C) U s s ∧
      FullAccount Gamma (web C) W U {s} ∧ SourcePredecessorRefines Gamma (web C) W U ∧
      (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x →
        IsRealTerminal (Gamma := web C) Gamma.graph.Adj U x) ∧
      (web C).vertexSet U = (web C).vertexSet W := by
  obtain ⟨U, hU, hUE, hUV, hUI, hUT, htrace⟩ := hW.isWarp.exists_edgeCut hedge hne
  have hV : (web C).vertexSet W ⊆ (web C).vertexSet U := le_of_eq hUV.symm
  have hE : familyEdges U ⊆ familyEdges W := hUE ▸ Set.sdiff_subset
  have hcut : familyEdges W \ {(s, t)} ⊆ familyEdges U := le_of_eq hUE.symm
  have hT : (web C).terminalFrontier U ⊆
      (web C).terminalFrontier W ∪ C.ladder.frontier a := by
    rw [hUT]
    exact Set.union_subset_union_right _ (Set.singleton_subset_iff.mpr hs)
  have hcover : Gamma.source ⊆ (web C).initialSet U ∪ Gamma.initialSet
      (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
        referencePathsMeeting C.ladder.limitWarp ((web C).vertexSet U)) := by
    intro x hx
    rcases hW.covers_source hx with hxI | hxR
    · exact Or.inl (hUI hxI)
    · exact Or.inr (by simpa only [hUV] using hxR)
  have hBlueprint : IsBlueprint C a U := of_roofed_fields hU
    (by simpa only [hUV] using hW.vertices_roofed) hcover
    (by simpa only [hUV] using hW.card_vertices)
    (DWeb.infinitelyManyMarkedEdges_of_finite_rayTrace hW.infinitely_many_marked htrace) (by
      intro x hx
      rcases hT hx with hxOld | hxFrontier
      · exact hW.terminals_popular hxOld
      · exact Or.inr hxFrontier)
  have hsReal := isRealTerminal_of_nonreal_outgoing hW.isWarp hedge hn
  have hrealE := realEdges_subset_of_cut hsReal hcut
  have hsV : s ∈ (web C).vertexSet U := hV (familyEdges_subset_vertexSet_prod W hedge).1
  have hreach : RealReach Gamma (web C) U s s := RealReach.refl hsV
  have hterminal : s ∈ (web C).terminalFrontier U := by
    rw [hUT]
    exact Or.inr (Set.mem_singleton s)
  have haccount : FullAccount Gamma (web C) W U {s} :=
    fullAccount_of_cut_and_reach hW.isWarp hcut
      (by rw [hUT]; exact Set.sdiff_subset.trans Set.subset_union_left)
      ⟨s, Set.mem_singleton s, hreach⟩
  refine ⟨U, hBlueprint, ⟨hUI, hV, hrealE, hT⟩, hterminal, hreach, haccount,
    (fun _ _ _ he ↦ Or.inl (hE he)), ?_, hUV⟩
  intro x hx
  exact ⟨hV hx.1, fun ⟨y, hy, hreal⟩ ↦ hx.2 ⟨y, hE hy, hreal⟩⟩

#print axioms IsBlueprint.exists_frontierCut

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
