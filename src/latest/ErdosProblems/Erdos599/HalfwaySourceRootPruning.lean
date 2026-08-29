/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause
import ErdosProblems.Erdos599.CountableAssignment

/-!
# Pruning a final blueprint to its source-rooted components

The moving construction may temporarily create components whose initial
vertices are not original sources.  At the final stage these components can
be discarded.  This file records that this pruning preserves all six
blueprint conditions, stability, and every designated original source.

This operation does not remove ray components rooted at an original source;
endpoint purity remains a separate final-geometry obligation.
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

/-- Keep exactly the blueprint paths whose initial vertex is an original
source of `Gamma`. -/
def sourceRootBlueprint (U : LinkageBlueprint Gamma Y kappa) :
    LinkageBlueprint Gamma Y kappa where
  paths := U.restrictInitial Gamma.source
  isWarp := by
    intro p hp q hq hpq
    exact U.isWarp hp.1 hq.1 hpq

@[simp] theorem sourceRootBlueprint_paths
    (U : LinkageBlueprint Gamma Y kappa) :
    (sourceRootBlueprint U).paths = U.restrictInitial Gamma.source :=
  rfl

@[simp] theorem sourceRootBlueprint_initialSet
    (U : LinkageBlueprint Gamma Y kappa) :
    (sourceRootBlueprint U).initialSet = U.initialSet ∩ Gamma.source := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp.1, rfl⟩, hp.2⟩
  · rintro ⟨⟨p, hp, rfl⟩, hsource⟩
    exact ⟨p, ⟨hp, hsource⟩, rfl⟩

theorem sourceRootBlueprint_initialSet_subset_source
    (U : LinkageBlueprint Gamma Y kappa) :
    (sourceRootBlueprint U).initialSet ⊆ Gamma.source := by
  rw [sourceRootBlueprint_initialSet]
  exact Set.inter_subset_right

theorem sourceRootBlueprint_vertexSet_subset
    (U : LinkageBlueprint Gamma Y kappa) :
    (sourceRootBlueprint U).vertexSet ⊆ U.vertexSet := by
  rintro x ⟨p, hp, hxp⟩
  exact ⟨p, hp.1, hxp⟩

theorem sourceRootBlueprint_edgeSet_subset
    (U : LinkageBlueprint Gamma Y kappa) :
    (sourceRootBlueprint U).edgeSet ⊆ U.edgeSet := by
  intro e he
  rcases Set.mem_iUnion.1 he with ⟨p, he⟩
  rcases Set.mem_iUnion.1 he with ⟨hp, he⟩
  exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp.1, he⟩⟩

theorem sourceRootBlueprint_terminalSet_subset
    (U : LinkageBlueprint Gamma Y kappa) :
    (sourceRootBlueprint U).terminalSet ⊆ U.terminalSet := by
  rintro x ⟨p, hp, hterminal⟩
  exact ⟨p, hp.1, hterminal⟩

theorem retainedReferenceInitials_subset_sourceRootBlueprint
    (U : LinkageBlueprint Gamma Y kappa) (T : Set V) :
    U.retainedReferenceInitials T ⊆
      (sourceRootBlueprint U).retainedReferenceInitials T := by
  rintro x ⟨p, hp, rfl⟩
  refine ⟨p, ⟨hp.1, ?_⟩, rfl⟩
  intro hmeet
  apply hp.2
  refine ⟨hmeet.1, ?_⟩
  rcases hmeet.2 with ⟨z, hzp, hzCarrier⟩
  exact ⟨z, hzp, sourceRootBlueprint_vertexSet_subset U hzCarrier⟩

/-- Pruning to original-source roots preserves all six conditions of a
linkage blueprint. -/
theorem sourceRootBlueprint_isLinkageBlueprint
    (U : LinkageBlueprint Gamma Y kappa) {T Z persistent : Set V}
    (hU : U.IsLinkageBlueprint T Z persistent) :
    (sourceRootBlueprint U).IsLinkageBlueprint T Z persistent where
  vertices_roofed := (sourceRootBlueprint_vertexSet_subset U).trans
    hU.vertices_roofed
  covers_source := by
    intro x hx
    rcases hU.covers_source hx with hxInitial | hxRetained
    · exact Or.inl (by
        rw [sourceRootBlueprint_initialSet]
        exact ⟨hxInitial, hx⟩)
    · exact Or.inr
        (retainedReferenceInitials_subset_sourceRootBlueprint U T hxRetained)
  vertices_closed := (sourceRootBlueprint_vertexSet_subset U).trans
    hU.vertices_closed
  card_paths :=
    (Cardinal.mk_subtype_mono (fun _ hp ↦ hp.1)).trans hU.card_paths
  infinitely_many_strong := by
    intro r hr
    exact hU.infinitely_many_strong r hr.1
  terminals_popular := (sourceRootBlueprint_terminalSet_subset U).trans
    hU.terminals_popular

/-- Stability is inherited when components are discarded. -/
theorem sourceRootBlueprint_stable
    (U : LinkageBlueprint Gamma Y kappa) {T persistent : Set V}
    (hU : U.Stable T persistent) :
    (sourceRootBlueprint U).Stable T persistent := by
  rintro x ⟨hxTerminal, hxT⟩
  exact hU ⟨sourceRootBlueprint_terminalSet_subset U hxTerminal, hxT⟩

/-- Every designated initial vertex which was already present survives
source-root pruning. -/
theorem designated_initial_sourceRootBlueprint
    (U : LinkageBlueprint Gamma Y kappa) {A : Set V}
    (hA : A ⊆ Gamma.source) (hinitial : A ⊆ U.initialSet) :
    A ⊆ (sourceRootBlueprint U).initialSet := by
  intro x hx
  rw [sourceRootBlueprint_initialSet]
  exact ⟨hinitial hx, hA hx⟩

/-- A finite source-rooted component of an edge-real blueprint contains no
original source except its initial vertex. -/
theorem sourceRootBlueprint_finitePath_source_pure
    (U : LinkageBlueprint Gamma Y kappa)
    (hGamma : Gamma.IsNormalized) (hreal : U.IsEdgeReal)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (Sum.inl q : DirectedPath.Path
      (imaginaryGraph Gamma Y kappa)) ∈ (sourceRootBlueprint U).paths) :
    q.support ∩ Gamma.source = {q.start} := by
  ext x
  constructor
  · rintro ⟨hxSupport, hxSource⟩
    have hx := Alternating.finitePath_eq_start_of_mem_support_of_mem_source hGamma
      (U.realFinitePath hreal q hq.1)
      (by simpa only [U.support_realFinitePath] using hxSupport) hxSource
    simpa only [U.start_realFinitePath, Set.mem_singleton_iff] using hx
  · intro hx
    have hxeq : x = q.start := by simpa only [Set.mem_singleton_iff] using hx
    subst x
    refine ⟨q.start_mem_support, ?_⟩
    exact hq.2

end LinkageBlueprint
end Blueprint
end Erdos599
