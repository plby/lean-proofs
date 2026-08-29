/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySourceRootEndpoint

/-!
# Target links from a ray-free source-rooted blueprint

Source purity and target linking do not require purity with respect to an
outer stopover.  This separates the valid target-link conclusion of the
fair scheduler from the false assertion that no completed path meets the
chosen ladder frontier internally.
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

/-- A ray-free source-rooted, edge-real blueprint whose terminals lie in
the original target retains the target-link certificate for every
designated initial source.  No stopover-purity premise is used. -/
theorem sourceRootBlueprint_blueprintLinksToTarget_of_noRay
    (U : LinkageBlueprint Gamma Y kappa)
    (hGamma : Gamma.IsNormalized) (hreal : U.IsEdgeReal)
    (hnoRay : ¬ ContainsDirectedRay U.edgeSet)
    {A0 : Set V}
    (hA0 : A0 ⊆ Gamma.source)
    (hinitial : A0 ⊆ (sourceRootBlueprint U).initialSet)
    (htarget : (sourceRootBlueprint U).realPart.terminals ⊆ Gamma.target) :
    (sourceRootBlueprint U).BlueprintLinksToTarget A0 := by
  intro a ha
  obtain ⟨p, hp, hpa⟩ := hinitial ha
  obtain ⟨q, hpq⟩ := allFinite_of_no_directedRay
    (sourceRootBlueprint U) (sourceRootBlueprint_no_directedRay U hnoRay)
      p hp
  subst p
  have hstart : q.start = a := by
    change q.start = a at hpa
    exact hpa
  have hsource : q.support ∩ Gamma.source = {q.start} :=
    sourceRootBlueprint_finitePath_source_pure U hGamma hreal q hp
  refine ⟨.inl q, hp, q, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA0⟩
      have hx : x ∈ q.support ∩ Gamma.source := ⟨hxq, hA0 hxA0⟩
      have hxStart : x ∈ ({q.start} : Set V) := hsource ▸ hx
      exact Set.mem_singleton_iff.2
        ((Set.mem_singleton_iff.1 hxStart).trans hstart)
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.1 hx
      subst x
      refine ⟨?_, ha⟩
      rw [← hstart]
      exact q.start_mem_support
  · have hfinishTerminal :
        q.finish ∈ (sourceRootBlueprint U).terminalSet :=
      ⟨.inl q, hp, (imaginaryWeb Gamma Y kappa).terminal?_finite q⟩
    have hfinish : q.finish ∈ Gamma.target :=
      htarget (terminalSet_subset_realPart_terminals_general
        (sourceRootBlueprint U) hfinishTerminal)
    have hsplit : q.walk.support = q.start :: q.walk.support.tail := by
      simpa only [q.walk.head_support] using
        (List.cons_head_tail q.walk.support_ne_nil).symm
    have hsplit' : q.walk.support = a :: q.walk.support.tail := by
      simpa only [hstart] using hsplit
    refine ⟨[], q.walk.support.tail, by simpa using hsplit',
      q.finish, hfinish, ?_⟩
    rw [← hsplit']
    exact q.finish_mem_support

end LinkageBlueprint
end Blueprint
end Erdos599
