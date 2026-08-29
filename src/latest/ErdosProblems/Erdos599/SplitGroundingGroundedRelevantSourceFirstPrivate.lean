/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantSourceFirst
import ErdosProblems.Erdos599.GroundingPrivatePathBoundaryStop

/-!
# Private witnesses for the source-first relevant frontier

Membership in the source-first relevant frontier already stores an ambient
source path having no earlier point of the larger relevant boundary.  Since
the source-first frontier is a subset of that larger boundary, the stored
path meets the source-first frontier exactly at its finish.  This makes the
private witness, and the resulting exclusion of boundary-valued incoming
tails, available without any minimal-separator choice.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev SourceFirstPrivateInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :=
  L.splitGroundedPopularAuxiliaryInput hL

private abbrev SourceFirstPrivateLV
    (L : Gamma.KappaLadder kappa) (_hL : L.IsSplitLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords

/-- Every source-first boundary point has its literal stored source path as
a private witness for the whole source-first frontier. -/
theorem splitGroundedRelevantSourceFirstBB_exists_privatePath
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (SourceFirstPrivateLV L hL)) {t : V}
    (ht : t ∈ L.splitGroundedRelevantSourceFirstBB hL C) :
    ∃ R : FinitePath Gamma.graph,
      R.start ∈ Gamma.source ∧
      R.finish = t ∧
      R.support ⊆ (SourceFirstPrivateInput L hL).roofRegion ∧
      R.support ∩ L.splitGroundedRelevantSourceFirstBB hL C = {t} := by
  obtain ⟨R, hsource, hfinish, hroof, _htRelevant, hfirst⟩ := ht
  refine ⟨R, hsource, hfinish, hroof, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    apply Set.mem_singleton_iff.2
    by_contra hxt
    have hxFinish : x ≠ R.finish := by
      simpa only [hfinish] using hxt
    have hxLast : x ≠ R.walk.support.getLast R.walk.support_ne_nil := by
      simpa only [R.walk.getLast_support] using hxFinish
    exact hfirst x
      (List.mem_dropLast_of_mem_of_ne_getLast hx.1 hxLast)
      (L.splitGroundedRelevantSourceFirstBB_subset hL C hx.2)
  · intro x hx
    have hxt : x = t := Set.mem_singleton_iff.1 hx
    subst x
    exact ⟨hfinish ▸ R.finish_mem_support,
      ⟨R, hsource, hfinish, hroof, _htRelevant, hfirst⟩⟩

/-- On the canonical private witness of a source-first boundary point, the
tail of every incoming edge is outside the source-first stopping set. -/
theorem splitGroundedRelevantSourceFirstBB_exists_privatePath_edgeTails
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (SourceFirstPrivateLV L hL)) {t : V}
    (ht : t ∈ L.splitGroundedRelevantSourceFirstBB hL C) :
    ∃ R : FinitePath Gamma.graph,
      R.start ∈ Gamma.source ∧
      R.finish = t ∧
      R.support ⊆ (SourceFirstPrivateInput L hL).roofRegion ∧
      (∀ {u v : V}, (u, v) ∈ R.edgeSet →
        u ∉ L.splitGroundedRelevantSourceFirstBB hL C) := by
  obtain ⟨R, hsource, hfinish, hroof, hprivate⟩ :=
    L.splitGroundedRelevantSourceFirstBB_exists_privatePath hL C ht
  refine ⟨R, hsource, hfinish, hroof, ?_⟩
  intro u v huv
  exact
    GroundingPrivatePathBoundaryStop.edge_tail_not_mem_of_private_superpath
      R R (L.splitGroundedRelevantSourceFirstBB hL C) t
      hprivate Set.Subset.rfl hfinish huv

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedRelevantSourceFirstBB_exists_privatePath
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedRelevantSourceFirstBB_exists_privatePath_edgeTails
