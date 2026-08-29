/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointFrontierCut

/-!
# Resolving an actual nonreal endpoint edge

The imaginary-edge definition supplies the captured large hammock. A
frontier tail is handled by an exact edge cut; every other roofed tail is
strictly roofed. The source path then either reaches a genuine full
frontier terminal or connects to the old head. A connector is not declared
terminal just because its finish happens to lie on the frontier.
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

theorem IsBlueprint.exists_nonrealEdge_resolution (hW : IsBlueprint C a W)
    (ha : a ∈ C.club) {s t : V} (hne : s ≠ t)
    (hedge : (s, t) ∈ familyEdges W) (hn : ¬Gamma.graph.Adj s t) :
    ∃ U : Set (web C).DPath, IsBlueprint C a U ∧
      RealAdvance Gamma (web C) W U (C.ladder.frontier a) ∧
      ((∃ z ∈ C.ladder.frontier a,
          z ∈ (web C).terminalFrontier U ∧ RealReach Gamma (web C) U s z ∧
          FullAccount Gamma (web C) W U {z}) ∨
        (RealReach Gamma (web C) U s t ∧ FullAccount Gamma (web C) W U {t} ∧
          familyEdges W \ {(s, t)} ⊆ familyEdges U ∧
          (web C).terminalFrontier W ⊆ (web C).terminalFrontier U)) ∧
      (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x → x ≠ s →
        IsRealTerminal (Gamma := web C) Gamma.graph.Adj U x) ∧
      SourcePredecessorRefines Gamma (web C) W U := by
  by_cases hsFrontier : s ∈ C.ladder.frontier a
  · obtain ⟨U, hU, hAdvance, hsTerminal, hreach, haccount, hpred, hterms, _hUV⟩ :=
      hW.exists_frontierCut hedge hne hn hsFrontier
    exact ⟨U, hU, hAdvance, Or.inl ⟨s, hsFrontier, hsTerminal, hreach, haccount⟩,
      (fun x hx _ ↦ hterms x hx), hpred⟩
  · have hsV := (familyEdges_subset_vertexSet_prod W hedge).1
    have hsStrict : s ∈ Gamma.strictRoof (C.ladder.frontier a) := by
      refine ⟨hW.vertices_roofed hsV, ?_⟩
      rw [C.ladder.frontiersAreEssential_of_roofsSourceAtStages C.legal.roofsSourceAtStages a]
      exact hsFrontier
    have hadj : (web C).graph.Adj s t := familyEdges_subset_adj W hedge
    have hHuge : ColouredSafeEndpointHammock.IsImaginary C.ladder.limitWarp
        (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa s t :=
      hadj.resolve_left hn
    obtain ⟨A, _hA, p, U, hU, _hps, _hpne, hpEnd, _hpE, hcut, _hV, _hI, hT,
        _hpNondeg, hledger, _hpV, hreach, haccount, hpred, hpTerminal, hAdvance,
        _hCarrier⟩ :=
      hW.exists_finiteReplacement ha hedge hne hsStrict hHuge
    have hsReal := isRealTerminal_of_nonreal_outgoing hW.isWarp hedge hn
    refine ⟨U, hU, hAdvance hsReal, ?_, (hledger hsReal).2.1, hpred⟩
    by_cases hpt : p.finish = t
    · exact Or.inr ⟨hpt ▸ hreach, hpt ▸ haccount, hcut, hT⟩
    · exact Or.inl ⟨p.finish, hpEnd.resolve_right hpt, hpTerminal hpt, hreach, haccount⟩

#print axioms IsBlueprint.exists_nonrealEdge_resolution

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
