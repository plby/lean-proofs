/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySourceRootPruningTerminal
import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Endpoint purity for a source-rooted final blueprint

This module isolates the two genuine remaining endpoint conditions.  If the
pruned edge relation has no forward ray and every carrier point in the
chosen stopover is a relation sink, then normalized source incidence gives
the full pathwise source--stopover purity required by the final linkage.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A forward-ray-free blueprint has only finite path members. -/
theorem allFinite_of_no_directedRay
    (U : LinkageBlueprint Gamma Y kappa)
    (hnoRay : ¬ ContainsDirectedRay U.edgeSet) :
    ∀ p ∈ U.paths,
      ∃ q : FinitePath (imaginaryGraph Gamma Y kappa), p = .inl q := by
  intro p hp
  rcases p with q | r
  · exact ⟨q, rfl⟩
  · apply False.elim
    apply hnoRay
    refine ⟨{ vertex := r.toFun, injective := r.injective }, ?_⟩
    rintro e ⟨n, rfl⟩
    exact Set.mem_iUnion.2 ⟨Sum.inr r,
      Set.mem_iUnion.2 ⟨hp, ⟨n, rfl⟩⟩⟩

/-- No-forward-ray is inherited when whole components are pruned. -/
theorem sourceRootBlueprint_no_directedRay
    (U : LinkageBlueprint Gamma Y kappa)
    (hnoRay : ¬ ContainsDirectedRay U.edgeSet) :
    ¬ ContainsDirectedRay (sourceRootBlueprint U).edgeSet := by
  rintro ⟨r, hr⟩
  exact hnoRay ⟨r, hr.trans (sourceRootBlueprint_edgeSet_subset U)⟩

/-- Endpoint purity for every retained component.  The proof uses edge
reality only to transport normalized-source purity back from the original
web; the stopover-side condition is stated directly on the blueprint edge
relation. -/
theorem sourceRootBlueprint_endpointPure_of_noRay_of_frontierSink
    (U : LinkageBlueprint Gamma Y kappa)
    (hGamma : Gamma.IsNormalized) (hreal : U.IsEdgeReal)
    (hnoRay : ¬ ContainsDirectedRay U.edgeSet)
    {C : Set V}
    (hterminal : (sourceRootBlueprint U).terminalSet ⊆ C)
    (hfrontierSink : ∀ x,
      x ∈ (sourceRootBlueprint U).vertexSet → x ∈ C →
        ¬ ∃ y, (x, y) ∈ (sourceRootBlueprint U).edgeSet) :
    ∀ p ∈ (sourceRootBlueprint U).paths,
      (sourceRootBlueprint U).IsPathBetween Gamma.source C p := by
  intro p hp
  obtain ⟨q, rfl⟩ := allFinite_of_no_directedRay
    (sourceRootBlueprint U) (sourceRootBlueprint_no_directedRay U hnoRay)
      p hp
  have hsourceOnly : q.support ∩ Gamma.source = {q.start} :=
    sourceRootBlueprint_finitePath_source_pure U hGamma hreal q hp
  have hfinishC : q.finish ∈ C := by
    apply hterminal
    refine ⟨Sum.inl q, hp, ?_⟩
    exact (imaginaryWeb Gamma Y kappa).terminal?_finite q
  have hfrontierOnly : q.support ∩ C = {q.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxSupport, hxC⟩
      apply Set.mem_singleton_iff.2
      by_contra hxFinish
      obtain ⟨y, hxy⟩ :=
        Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish q
          hxSupport hxFinish
      apply hfrontierSink x ⟨Sum.inl q, hp, hxSupport⟩ hxC
      exact ⟨y, Set.mem_iUnion.2 ⟨Sum.inl q,
        Set.mem_iUnion.2 ⟨hp, hxy⟩⟩⟩
    · intro x hx
      have hxeq : x = q.finish := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨q.finish_mem_support, hfinishC⟩
  have hboundaryOnly :
      q.support ∩ (Gamma.source ∪ C) = {q.start, q.finish} := by
    rw [Set.inter_union_distrib_left, hsourceOnly, hfrontierOnly]
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  exact ⟨q, rfl, hboundaryOnly, hsourceOnly⟩

end LinkageBlueprint
end Blueprint
end Erdos599
