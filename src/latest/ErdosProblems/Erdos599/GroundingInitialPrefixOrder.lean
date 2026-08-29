/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceFirstOrder
import ErdosProblems.Erdos599.GroundingFragmentResidualOrder

/-!
# Exact support and edge coverage of initial finite prefixes

The coordinate and prefix-length lemmas are reused from the existing
source-first order module. All statements here are about an arbitrary
finite path or ray, with no ladder or grounding-control hypotheses.
-/

namespace Erdos599.GroundingInitialPrefixOrder

open Set DirectedPath Alternating
open DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation

universe u

variable {V : Type u} {G : DWeb V}

/-- A walk made of edges of a simple path respects its intrinsic order. -/
theorem walk_beforeEq_of_edges_subset (P : G.DPath) {x y : V}
    (w : Walk G.graph x y) (hx : x ∈ P.support) (hE : w.edgeSet ⊆ P.edgeSet) :
    GroundingCut.BeforeEq P x y := by
  induction w with
  | nil => exact GroundingCut.beforeEq_refl hx
  | @cons x z y e w ih =>
      have hxz := hE (Or.inl rfl)
      exact GroundingFragmentResidualOrder.beforeEq_trans
        (GroundingErasedDecode.GroundingCut.beforeEq_of_mem_edgeSet hxz)
        (ih (P.edgeSet_subset_support_prod hxz).2 (fun _ he ↦ hE (Or.inr he)))

/-- A finite initial prefix contains exactly the vertices at or before its finish. -/
theorem mem_support_iff_beforeEq_finish (P : G.DPath) (q : FinitePath G.graph)
    (hstart : q.start = P.initial) (hsub : q.IsSubpathOf P) {x : V} :
    x ∈ q.support ↔ GroundingCut.BeforeEq P x q.finish := by
  constructor
  · intro hx
    have ht := walk_beforeEq_of_edges_subset P (q.suffixFrom x hx).walk
      (by simpa only [FinitePath.suffixFrom_start] using hsub.1 hx)
      ((q.suffixFrom_edgeSet_subset x hx).trans hsub.2)
    simpa only [FinitePath.suffixFrom_start, FinitePath.suffixFrom_finish] using ht
  · intro hbefore
    have hxP : x ∈ P.support := by
      obtain ⟨m, n, hmx, _, _⟩ := hbefore
      exact GroundingCut.occursAt_mem_support hmx
    obtain ⟨r, hrs, hrt, _hrS, hrE⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix P hxP
    have hlen := initialSubpath_length_le_of_beforeEq_finish P r q hrs hstart hrE
      hsub.2 (hrt.symm ▸ hbefore)
    have hprefix := initialSubpath_isPrefixOf_of_length_le P r q hrs hstart hrE hsub.2 hlen
    exact hprefix.support_subset (hrt ▸ r.finish_mem_support)

/-- An edge survives precisely when its tail precedes the prefix endpoint strictly. -/
theorem mem_edgeSet_iff_before_finish (P : G.DPath) (q : FinitePath G.graph)
    (hstart : q.start = P.initial) (hsub : q.IsSubpathOf P) {x y : V} :
    (x, y) ∈ q.edgeSet ↔ (x, y) ∈ P.edgeSet ∧ GroundingCut.Before P x q.finish := by
  constructor
  · intro he
    refine ⟨hsub.2 he, ?_, ?_⟩
    · exact (mem_support_iff_beforeEq_finish P q hstart hsub).1
        (q.edgeSet_subset_support_prod he).1
    · exact (Walk.finish_ne_edge_source q.walk q.isPath he).symm
  · rintro ⟨he, hbefore, hne⟩
    exact FinitePath.outgoing_mem_of_isSubpathOf q P hsub
      ((mem_support_iff_beforeEq_finish P q hstart hsub).2 hbefore) hne he

#print axioms mem_support_iff_beforeEq_finish
#print axioms mem_edgeSet_iff_before_finish

end Erdos599.GroundingInitialPrefixOrder
