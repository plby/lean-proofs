/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingRelationalInterval
import ErdosProblems.Erdos599.SafeSwitchingDegenerateConfinement

/-!
# Relational interval-convex switching: endpoint confinement

This argument does not compile a matching traversal into a literal alternating
path. It uses the proved relational interval condition and exact local
biuniqueness. Construction of such a switching system remains separate.
-/

namespace Erdos599.Alternating.SwitchingCore.RelationalInterval

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

theorem finitePath_isFragmentOf_forwardWarp_of_incidence
    {W Y : Set Gamma.DPath} {R F E : Set (V × V)}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hF : F ⊆ familyEdges W)
    (hin : ∀ {a b x : V}, (a, x) ∈ F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hout : ∀ {x a b : V}, (x, a) ∈ F →
      (x, b) ∈ familyEdges Y → (x, b) ∈ R)
    (hE : E = (familyEdges Y \ R) ∪ F)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hinterval : ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p)
    (hpure : ∀ {x y : V}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y)
    (p : FinitePath Gamma.graph) (hpne : p.start ≠ p.finish)
    (hpE : p.edgeSet ⊆ E)
    (hstartOff : p.start ∉ Gamma.vertexSet Y)
    (hfinishOff : p.finish ∉ Gamma.vertexSet Y) :
    IsFragmentOf p W := by
  let B := familyEdges Y \ R
  have hpcover : p.edgeSet ⊆ B ∪ F := by
    simpa only [hE] using hpE
  have hstart : ∃ y, (p.start, y) ∈ F := by
    obtain ⟨y, hy⟩ :=
      FinitePath.exists_edge_from_of_mem_of_ne_finish p p.start_mem_support hpne
    rcases hpcover hy with hB | hF
    · exact (hstartOff (familyEdges_subset_vertexSet_prod Y hB.1).1).elim
    · exact ⟨y, hF⟩
  have hfinish : ∃ x, (x, p.finish) ∈ F := by
    obtain ⟨x, hx⟩ :=
      FinitePath.exists_edge_to_of_mem_of_ne_start p p.finish_mem_support hpne.symm
    rcases hpcover hx with hB | hF
    · exact (hfinishOff (familyEdges_subset_vertexSet_prod Y hB.1).2).elim
    · exact ⟨x, hF⟩
  have hdisj : Disjoint B F := retained_disjoint_inserted_of_incidence hin
  have hbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ B ∪ F) := by
    simpa only [hE] using hunique
  have hpF : p.edgeSet ⊆ F :=
    finitePath_edgeSet_subset_right_of_noForwardSandwich B F hdisj hbi
      (noForwardSandwich_of_incidence_intervalConvex hY hin hout hinterval hpure)
      p hpcover hstart hfinish
  exact finitePath_isFragmentOf_of_edgeSet_subset_familyEdges hW p hpne
    (hpF.trans hF)

/-- Backwards-compatible disjoint-edge specialization. -/
theorem finitePath_isFragmentOf_forwardWarp
    {W Y : Set Gamma.DPath} {R F E : Set (V × V)}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (_hR : R ⊆ familyEdges Y) (hF : F ⊆ familyEdges W)
    (hFdisj : Disjoint F (familyEdges Y))
    (hE : E = (familyEdges Y \ R) ∪ F)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hinterval : ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p)
    (hpure : ∀ {x y : V}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y)
    (p : FinitePath Gamma.graph) (hpne : p.start ≠ p.finish)
    (hpE : p.edgeSet ⊆ E)
    (hstartOff : p.start ∉ Gamma.vertexSet Y)
    (hfinishOff : p.finish ∉ Gamma.vertexSet Y) :
    IsFragmentOf p W :=
  finitePath_isFragmentOf_forwardWarp_of_incidence hW hY hF
    (incoming_mem_removed hE hunique hFdisj)
    (outgoing_mem_removed hE hunique hFdisj) hE hunique hinterval hpure
    p hpne hpE hstartOff hfinishOff

#print axioms finitePath_isFragmentOf_forwardWarp_of_incidence
#print axioms finitePath_isFragmentOf_forwardWarp

end Erdos599.Alternating.SwitchingCore.RelationalInterval
