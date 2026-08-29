/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularSafeCompletion
import ErdosProblems.Erdos599.SafeLinkCertifiedChoice

/-!
# Residual safe completions retaining the Section 6 tree certificate

For a normalized ambient web, vertex deletion remains normalized.  The
certified form of Theorem 6.1 can therefore be applied directly in the
current residual, and its selected path can be lifted to the ambient web.
This file packages that lifted ordinary safe completion together with the
maximal residual tree and boundary waves from which it was selected.
-/

noncomputable section

namespace Erdos599
namespace CardinalInduction
namespace SingularCertifiedSafeCompletion

open RegularSafeCompletion
open Set DirectedPath

universe u

variable {V : Type u}

/-- An ordinary ambient safe completion together with the certified
residual path from which it was obtained. -/
structure CertifiedSafeCompletionChoice
    (G : DWeb V) (frozen : Set V) (a : V) where
  completion : SafeCompletionChoice G frozen a
  certificate : SafeLink.CertifiedSafeTargetPath (G.delete frozen) a
  path_eq_lift : completion.path =
    certificate.path.lift (fun {_ _} h ↦ G.delete_adj_imp h)

/-- The certified Section 6 choice lifts to the exact safe-completion type
consumed by completed-row recursions. -/
theorem exists_certifiedSafeCompletionChoice
    (G : DWeb V) (hNorm : G.IsNormalized) (frozen : Set V) {a : V}
    (hresidual : (G.delete frozen).IsUnhindered)
    (haSource : a ∈ G.source) (haFresh : a ∉ frozen) :
    Nonempty (CertifiedSafeCompletionChoice G frozen a) := by
  let H := G.delete frozen
  have hHNorm : H.IsNormalized := by
    intro x y hxy
    exact ⟨fun hy ↦ (hNorm hxy.1).1 hy.1,
      fun hx ↦ (hNorm hxy.1).2 hx.1⟩
  have haH : a ∈ H.source := ⟨haSource, haFresh⟩
  obtain ⟨C⟩ := SafeLink.exists_certifiedSafeTargetPath
    H hHNorm hresidual haH
  let q := C.path
  have hqStart : q.start = a := by
    simpa only [q] using C.path_start
  have hqFinish : q.finish = C.targetVertex := by
    simpa only [q] using C.path_finish
  let p : FinitePath G.graph := q.lift (fun {_ _} h ↦ G.delete_adj_imp h)
  have hpSupport : p.support = q.support := by
    exact FinitePath.support_lift _ q
  have hpAvoid : Disjoint p.support frozen := by
    change Disjoint (G.liftDeletePath frozen (.inl q)).support frozen
    apply G.liftDeletePath_avoids frozen (.inl q)
    change q.start ∉ frozen
    rw [C.path_start]
    exact haFresh
  have hpSourcePure : p.support ∩ G.source = {p.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxSource⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_start_of_mem_walk p.walk hxp hxSource)
    · intro x hx
      have hxStart : x = p.start := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨p.start_mem_support, ?_⟩
      change q.start ∈ G.source
      rw [hqStart]
      exact haSource
  have hpTargetPure : p.support ∩ G.target = {p.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxTarget⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_finish_of_mem_walk p.walk hxp hxTarget)
    · intro x hx
      have hxFinish : x = p.finish := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨p.finish_mem_support, ?_⟩
      change q.finish ∈ G.target
      rw [hqFinish]
      exact C.targetVertex_mem_target.1
  let completion : SafeCompletionChoice G frozen a :=
    { path := p
      start_eq := by
        simpa only [p, FinitePath.lift] using hqStart
      start_source := by
        change q.start ∈ G.source
        rw [hqStart]
        exact haSource
      finish_target := by
        change q.finish ∈ G.target
        rw [hqFinish]
        exact C.targetVertex_mem_target.1
      source_pure := hpSourcePure
      target_pure := hpTargetPure
      avoids := hpAvoid
      next_unhindered := by
        rw [← G.delete_delete]
        simpa [H, hpSupport] using C.path_safe.2.2 }
  exact ⟨{
    completion := completion
    certificate := C
    path_eq_lift := rfl }⟩

#print axioms exists_certifiedSafeCompletionChoice

end SingularCertifiedSafeCompletion
end CardinalInduction
end Erdos599
