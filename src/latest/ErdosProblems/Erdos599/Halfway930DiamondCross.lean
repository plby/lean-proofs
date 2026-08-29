/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930FreshPath
import ErdosProblems.Erdos599.HalfwaySourceFrontAbsorption
import ErdosProblems.Erdos599.HalfwayCompleteInsideCross

/-!
# Old-head incidence of the concrete 9.30 diamond

The concrete coupled 9.30 replacement is a literal finite diamond.  Its new
path meets the cut carrier only at its initial vertex, so no new diamond edge
can enter an old vertex.  Moreover, if the appended path is a member of the
later row relation, every diamond edge has the exact old-or-row provenance
used by the complete 9.31 inside-union compiler.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- No edge newly introduced by a fresh finite diamond enters the old
carrier. -/
theorem diamond_noNewIncomingOld
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish}) :
    ∀ {x y : V}, x ∈ W.vertexSet →
      (y, x) ∈ (W.diamond q hq P hstart hfresh).edgeSet →
        (y, x) ∈ W.edgeSet := by
  intro x y hx hyx
  rw [edgeSet_diamond] at hyx
  rcases hyx with hyx | hyx
  · exact hyx
  · have hxP : x ∈ P.support :=
      (P.edgeSet_subset_support_prod hyx).2
    have hxFinish : x = q.finish :=
      Set.mem_singleton_iff.1 (hfresh ⟨hx, hxP⟩)
    have hxStart : x = P.start := hxFinish.trans hstart.symm
    exact False.elim
      (FinitePath.no_incoming_edge_at_start P y (hxStart ▸ hyx))

/-- The cut version is the actual imaginary-successor 9.30 branch.  The cut
has the same carrier as the incoming blueprint and only deletes an edge. -/
theorem diamondAfterCut_noNewIncomingOld
    {W cut : LinkageBlueprint Gamma Y kappa} {u : V}
    (hcut : W.IsCutAt cut u)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ cut.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : cut.vertexSet ∩ P.support ⊆ {q.finish}) :
    ∀ {x y : V}, x ∈ W.vertexSet →
      (y, x) ∈ (cut.diamond q hq P hstart hfresh).edgeSet →
        (y, x) ∈ W.edgeSet := by
  intro x y hx hyx
  have hxCut : x ∈ cut.vertexSet := by
    rw [SourceFrontAbsorption.cut_vertexSet_eq hcut]
    exact hx
  exact SourceFrontAbsorption.cut_edgeSet_subset hcut
    (diamond_noNewIncomingOld cut q hq P hstart hfresh hxCut hyx)

/-- If the appended finite path is a literal later-row path, every diamond
edge is either an old edge or a later-row edge. -/
theorem diamond_edgeSet_subset_old_union_row
    (W row : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish})
    (hProw : P.edgeSet ⊆ row.edgeSet) :
    (W.diamond q hq P hstart hfresh).edgeSet ⊆
      W.edgeSet ∪ row.edgeSet := by
  intro e he
  rw [edgeSet_diamond] at he
  exact he.elim Or.inl (fun h ↦ Or.inr (hProw h))

/-- Old-or-row provenance after the exact one-edge cut. -/
theorem diamondAfterCut_edgeSet_subset_old_union_row
    {W cut : LinkageBlueprint Gamma Y kappa} {u : V}
    (hcut : W.IsCutAt cut u)
    (row : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ cut.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : cut.vertexSet ∩ P.support ⊆ {q.finish})
    (hProw : P.edgeSet ⊆ row.edgeSet) :
    (cut.diamond q hq P hstart hfresh).edgeSet ⊆
      W.edgeSet ∪ row.edgeSet := by
  intro e he
  rw [edgeSet_diamond] at he
  rcases he with he | he
  · exact Or.inl (SourceFrontAbsorption.cut_edgeSet_subset hcut he)
  · exact Or.inr (hProw he)

#print axioms diamond_noNewIncomingOld
#print axioms diamondAfterCut_noNewIncomingOld
#print axioms diamondAfterCut_edgeSet_subset_old_union_row

end Erdos599.Blueprint.LinkageBlueprint
