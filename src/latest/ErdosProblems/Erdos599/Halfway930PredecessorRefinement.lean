/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930DiamondGeometry
import ErdosProblems.Erdos599.IntermediateRelationLimitRefinement

/-!
# Predecessor refinement for cuts and terminal diamonds

The exact edge cut and a fresh terminal diamond satisfy the old-edge branch
of predecessor refinement. Their composition is compatible with the weaker
real-subdivision branch needed for imaginary-edge replacements.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

theorem IsCutAt.predecessorRefines_cut
    {W cut : LinkageBlueprint Gamma Y kappa} {u : V}
    (hcut : W.IsCutAt cut u) : W.PredecessorRefines cut := by
  intro x y _ hyx
  exact Or.inl (hcut.ordinaryExtends_original.2 hyx)

theorem predecessorRefines_diamond
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish}) :
    W.PredecessorRefines (W.diamond q hq P hstart hfresh) := by
  intro x y hx hyx
  rw [edgeSet_diamond] at hyx
  rcases hyx with hyx | hyx
  · exact Or.inl hyx
  · have hxP : x ∈ P.support := (P.edgeSet_subset_support_prod hyx).2
    have hxeq : x = q.finish := Set.mem_singleton_iff.1 (hfresh ⟨hx, hxP⟩)
    have hyStart : (y, P.start) ∈ P.edgeSet := by
      simpa only [hstart, hxeq] using hyx
    exact False.elim (Alternating.FinitePath.no_incoming_edge_at_start P y hyStart)

/-- Cutting an imaginary edge and appending at its tail retains the
refinement invariant relative to the original blueprint. -/
theorem predecessorRefines_cut_diamond
    {W cut : LinkageBlueprint Gamma Y kappa} {u : V}
    (hcut : W.IsCutAt cut u)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ cut.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : cut.vertexSet ∩ P.support ⊆ {q.finish}) :
    W.PredecessorRefines (cut.diamond q hq P hstart hfresh) := by
  refine PredecessorRefines.trans hcut.predecessorRefines_cut
    (predecessorRefines_diamond cut q hq P hstart hfresh) ?_
    (ordinaryExtends_diamond cut q hq P hstart hfresh).realPart_extends.2
  rcases hcut with ⟨_, rfl⟩ | ⟨v, hv⟩
  · exact Set.Subset.rfl
  · intro x hx
    simpa only [hv.vertices_eq] using hx

#print axioms IsCutAt.predecessorRefines_cut
#print axioms predecessorRefines_diamond
#print axioms predecessorRefines_cut_diamond

end Erdos599.Blueprint.LinkageBlueprint
