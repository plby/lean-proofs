/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySourceRootEndpoint

/-!
# Endpoint purity allowing source--stopover overlap

An initial point may also belong to the stopover.  Thus only non-source
stopover points on the final carrier must be sinks.
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

/-- Correct overlap-aware endpoint criterion for a source-rooted final
blueprint.  A carrier point in both the source and stopover may be the first
endpoint; every other stopover carrier point must be a sink. -/
theorem sourceRootBlueprint_endpointPure_of_noRay_of_nonSourceFrontierSink
    (U : LinkageBlueprint Gamma Y kappa)
    (hGamma : Gamma.IsNormalized) (hreal : U.IsEdgeReal)
    (hnoRay : ¬ ContainsDirectedRay U.edgeSet)
    {C : Set V}
    (hterminal : (sourceRootBlueprint U).terminalSet ⊆ C)
    (hfrontierSink : ∀ x,
      x ∈ (sourceRootBlueprint U).vertexSet → x ∈ C →
        x ∉ Gamma.source →
          ¬ ∃ y, (x, y) ∈ (sourceRootBlueprint U).edgeSet) :
    ∀ p ∈ (sourceRootBlueprint U).paths,
      (sourceRootBlueprint U).IsPathBetween Gamma.source C p := by
  intro p hp
  obtain ⟨q, rfl⟩ := allFinite_of_no_directedRay
    (sourceRootBlueprint U) (sourceRootBlueprint_no_directedRay U hnoRay)
      p hp
  have hsourceOnly : q.support ∩ Gamma.source = {q.start} :=
    sourceRootBlueprint_finitePath_source_pure U hGamma hreal q hp
  have hstartSource : q.start ∈ Gamma.source := by
    exact hp.2
  have hfinishC : q.finish ∈ C := by
    apply hterminal
    refine ⟨Sum.inl q, hp, ?_⟩
    exact (imaginaryWeb Gamma Y kappa).terminal?_finite q
  have hboundaryOnly :
      q.support ∩ (Gamma.source ∪ C) = {q.start, q.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxSupport, hxBoundary⟩
      rcases hxBoundary with hxSource | hxC
      · left
        have hx : x ∈ ({q.start} : Set V) :=
          hsourceOnly ▸ ⟨hxSupport, hxSource⟩
        exact Set.mem_singleton_iff.1 hx
      · by_cases hxSource : x ∈ Gamma.source
        · left
          have hx : x ∈ ({q.start} : Set V) :=
            hsourceOnly ▸ ⟨hxSupport, hxSource⟩
          exact Set.mem_singleton_iff.1 hx
        · right
          apply Set.mem_singleton_iff.2
          by_contra hxFinish
          obtain ⟨y, hxy⟩ :=
            Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
              q hxSupport hxFinish
          apply hfrontierSink x ⟨Sum.inl q, hp, hxSupport⟩ hxC hxSource
          exact ⟨y, Set.mem_iUnion.2 ⟨Sum.inl q,
            Set.mem_iUnion.2 ⟨hp, hxy⟩⟩⟩
    · intro x hx
      rcases Set.mem_insert_iff.1 hx with hstart | hfinish
      · subst x
        exact ⟨q.start_mem_support, Or.inl hstartSource⟩
      · have hxeq : x = q.finish := Set.mem_singleton_iff.1 hfinish
        subst x
        exact ⟨q.finish_mem_support, Or.inr hfinishC⟩
  exact ⟨q, rfl, hboundaryOnly, hsourceOnly⟩

end LinkageBlueprint
end Blueprint
end Erdos599
