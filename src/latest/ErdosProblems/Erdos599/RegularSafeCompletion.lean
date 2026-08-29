/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.SafeLinkPropositionComplete

/-!
# One safe completion step for the regular recursion

Completed target components in the regular construction are frozen forever.
Consequently an arbitrary target-reaching component is not a valid new
completed component: deleting its carrier need not preserve unhinderedness.
This file packages the source Theorem 6.1 construction in the exact residual
form needed by the completed/pending recursion.
-/

noncomputable section

namespace Erdos599
namespace CardinalInduction
namespace RegularSafeCompletion

open Set DirectedPath

universe u

variable {V : Type u}

/-- A target path safely chosen outside an already frozen carrier. -/
structure SafeCompletionChoice
    (G : DWeb V) (frozen : Set V) (a : V) where
  path : DirectedPath.FinitePath G.graph
  start_eq : path.start = a
  start_source : path.start ∈ G.source
  finish_target : path.finish ∈ G.target
  source_pure : path.support ∩ G.source = {path.start}
  target_pure : path.support ∩ G.target = {path.finish}
  avoids : Disjoint path.support frozen
  next_unhindered :
    (G.delete (frozen ∪ path.support)).IsUnhindered

/-- Apply Aharoni--Berger Theorem 6.1 in the current residual web.  The
result is normalized there to obtain endpoint purity and then lifted first
out of normalization and finally out of the frozen-vertex deletion. -/
theorem exists_safeCompletionChoice
    (G : DWeb V) (frozen : Set V) {a : V}
    (hresidual : (G.delete frozen).IsUnhindered)
    (haSource : a ∈ G.source) (haFresh : a ∉ frozen) :
    Nonempty (SafeCompletionChoice G frozen a) := by
  let H := G.delete frozen
  have haH : a ∈ H.source := ⟨haSource, haFresh⟩
  have haNorm : a ∈ H.normalized.source := haH
  have hsafeNorm : H.normalized.HasSafeTargetPath a :=
    SafeLink.exists_safeTargetPath H.normalized hresidual.normalized haNorm
  obtain ⟨q, hqSafe, hqSource, hqTarget⟩ :=
    SafeLink.exists_endpointPure_safeTargetPath_of_normalized H hsafeNorm
  dsimp only [H] at q hqSafe hqSource hqTarget
  let p : DirectedPath.FinitePath G.graph :=
    q.lift (fun {_ _} h ↦ G.delete_adj_imp h)
  have hpSupport : p.support = q.support := by simp [p]
  have hpAvoid : Disjoint p.support frozen := by
    change Disjoint (G.liftDeletePath frozen (.inl q)).support frozen
    apply G.liftDeletePath_avoids frozen (.inl q)
    change q.start ∉ frozen
    rw [hqSafe.1]
    exact haFresh
  have hpSourcePure : p.support ∩ G.source = {p.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxSource⟩
      have hxFresh : x ∉ frozen :=
        fun hx ↦ Set.disjoint_left.1 hpAvoid hxp hx
      have hxCurrent : x ∈ q.support ∩ (G.delete frozen).source := by
        exact ⟨by simpa [hpSupport] using hxp, hxSource, hxFresh⟩
      have hx := hqSource hxCurrent
      simpa only [p, DirectedPath.FinitePath.lift] using hx
    · rintro x hx
      have hxEq : x = p.start := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨p.start_mem_support, ?_⟩
      simpa only [p, DirectedPath.FinitePath.lift, hqSafe.1] using haSource
  have hpTargetPure : p.support ∩ G.target = {p.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxTarget⟩
      have hxFresh : x ∉ frozen :=
        fun hx ↦ Set.disjoint_left.1 hpAvoid hxp hx
      have hxCurrent : x ∈ q.support ∩ (G.delete frozen).target := by
        exact ⟨by simpa [hpSupport] using hxp, hxTarget, hxFresh⟩
      have hx := hqTarget hxCurrent
      simpa only [p, DirectedPath.FinitePath.lift] using hx
    · rintro x hx
      have hxEq : x = p.finish := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨p.finish_mem_support, ?_⟩
      simpa only [p, DirectedPath.FinitePath.lift] using hqSafe.2.1.1
  refine ⟨
    { path := p
      start_eq := by
        simpa only [p, DirectedPath.FinitePath.lift] using hqSafe.1
      start_source := by
        simpa only [p, DirectedPath.FinitePath.lift, hqSafe.1] using haSource
      finish_target := by
        simpa only [p, DirectedPath.FinitePath.lift] using hqSafe.2.1.1
      source_pure := hpSourcePure
      target_pure := hpTargetPure
      avoids := hpAvoid
      next_unhindered := ?_ }⟩
  rw [← G.delete_delete]
  simpa [H, hpSupport] using hqSafe.2.2

/-- The singleton ambient path selected by a safe completion step. -/
def SafeCompletionChoice.family
    {G : DWeb V} {frozen : Set V} {a : V}
    (c : SafeCompletionChoice G frozen a) : Set G.DPath :=
  {Sum.inl c.path}

theorem SafeCompletionChoice.vertexSet_family
    {G : DWeb V} {frozen : Set V} {a : V}
    (c : SafeCompletionChoice G frozen a) :
    G.vertexSet c.family = c.path.support := by
  ext x
  constructor
  · rintro ⟨p, hp, hxp⟩
    have hp' : p = .inl c.path := by
      simpa only [SafeCompletionChoice.family, Set.mem_singleton_iff] using hp
    subst p
    exact hxp
  · intro hxp
    exact ⟨.inl c.path, Set.mem_singleton _, hxp⟩

theorem SafeCompletionChoice.family_avoids
    {G : DWeb V} {frozen : Set V} {a : V}
    (c : SafeCompletionChoice G frozen a) :
    Disjoint (G.vertexSet c.family) frozen := by
  rw [c.vertexSet_family]
  exact c.avoids

/-- A safe completion choice is an exact singleton linkage from its scheduled
source to the ambient target. -/
theorem SafeCompletionChoice.family_isLinkageBetween
    {G : DWeb V} {frozen : Set V} {a : V}
    (c : SafeCompletionChoice G frozen a) :
    IsLinkageBetween G {a} G.target c.family := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    have hp' : p = (.inl c.path : G.DPath) := by
      simpa only [SafeCompletionChoice.family, Set.mem_singleton_iff] using hp
    have hq' : q = (.inl c.path : G.DPath) := by
      simpa only [SafeCompletionChoice.family, Set.mem_singleton_iff] using hq
    exact (hpq (hp'.trans hq'.symm)).elim
  · intro p hp
    have hp' : p = (.inl c.path : G.DPath) := by
      simpa only [SafeCompletionChoice.family, Set.mem_singleton_iff] using hp
    exact ⟨c.path, hp'⟩
  · ext x
    simp only [G.mem_initialSet, SafeCompletionChoice.family,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨p, rfl, hpx⟩
      exact hpx.symm.trans c.start_eq
    · rintro rfl
      exact ⟨.inl c.path, rfl, c.start_eq⟩
  · rintro x ⟨p, hp, hpx⟩
    have hp' : p = (.inl c.path : G.DPath) := by
      simpa only [SafeCompletionChoice.family, Set.mem_singleton_iff] using hp
    subst p
    have hx : x = c.path.finish := by
      exact Option.some.inj hpx.symm
    exact hx.symm ▸ c.finish_target
  · intro p hp
    have hp' : p = (.inl c.path : G.DPath) := by
      simpa only [SafeCompletionChoice.family, Set.mem_singleton_iff] using hp
    subst p
    refine ⟨c.path, rfl, ?_, ?_⟩
    · ext x
      constructor
      · rintro ⟨hxp, hxa | hxTarget⟩
        · exact Or.inl ((Set.mem_singleton_iff.mp hxa).trans c.start_eq.symm)
        · apply Or.inr
          apply Set.mem_singleton_iff.mp
          rw [← c.target_pure]
          exact ⟨hxp, hxTarget⟩
      · rintro (hxStart | hxFinish)
        · have hx : x = c.path.start := Set.mem_singleton_iff.mp hxStart
          subst x
          exact ⟨c.path.start_mem_support,
            Or.inl (Set.mem_singleton_iff.2 c.start_eq)⟩
        · have hx : x = c.path.finish := Set.mem_singleton_iff.mp hxFinish
          subst x
          exact ⟨c.path.finish_mem_support, Or.inr c.finish_target⟩
    · ext x
      constructor
      · rintro ⟨hxp, hxa⟩
        exact Set.mem_singleton_iff.2
          ((Set.mem_singleton_iff.mp hxa).trans c.start_eq.symm)
      · intro hxStart
        have hx : x = c.path.start := Set.mem_singleton_iff.mp hxStart
        subst x
        exact ⟨c.path.start_mem_support,
          Set.mem_singleton_iff.2 c.start_eq⟩

end RegularSafeCompletion
end CardinalInduction
end Erdos599
