/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.IndexedRelationLimitGeometry

/-!
# Final all-real geometry from proper-limit geometry and fairness

Deleting non-real limit edges can only add roots.  The carrier and retained
reference family do not change.  Fair terminal completion gives the exact
target-terminal conclusion, so no final IsLB certificate is postulated.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace IndexedRealExtensionChain

universe u v

variable {V : Type u} {I : Type v} [LinearOrder I] [Nonempty I]
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {B persistent : Set V}

/-- Removing non-real edges adds possible roots but removes none. -/
theorem eventualInitial_subset_realInitial
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.eventualRelationBlueprint.initialSet ⊆ C.realRelationBlueprint.initialSet := by
  rw [eventualRelationBlueprint, realRelationBlueprint,
    orientationBlueprint_initialSet_eq_no_incoming,
    orientationBlueprint_initialSet_eq_no_incoming,
    C.eventualRelationOrientation_spec.1, C.eventualRelationOrientation_spec.2,
    C.realRelationOrientation_spec.1, C.realRelationOrientation_spec.2]
  rintro x ⟨hx, hno⟩
  refine ⟨hx, ?_⟩
  rintro ⟨y, hy⟩
  exact hno ⟨y, C.realEdgeLimit_subset_eventualEdgeLimit hy⟩

theorem eventualRetainedReference_eq_realRetainedReference
    (C : IndexedRealExtensionChain I Gamma Y kappa B) (T : Set V) :
    C.eventualRelationBlueprint.retainedReferenceInitials T =
      C.realRelationBlueprint.retainedReferenceInitials T := by
  simp only [retainedReferenceInitials, C.eventualRelationBlueprint_vertexSet,
    C.realRelationBlueprint_vertexSet]

/-- All six final real blueprint fields follow from the proved proper
geometry and completion of every appearing real terminal. -/
theorem realRelationBlueprint_isLinkageBlueprint
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    {T Z : Set V}
    (hproper : C.eventualRelationBlueprint.IsLinkageBlueprint T Z persistent)
    (hkappa : aleph0 ≤ kappa)
    (hstrong : ∀ i, (C.stage i).InfinitelyManyStrongEdges)
    (hGamma : Gamma.IsNormalized) (hBtarget : B ⊆ Gamma.target)
    (hcompleted : ∀ i x, x ∈ (C.stage i).realPart.terminals →
      ∃ j, x ∈ (C.stage j).completedRealVertices B)
    (hB : B ∩ C.realVertexLimit ⊆ persistent) :
    C.realRelationBlueprint.IsLinkageBlueprint T Z persistent where
  vertices_roofed := by
    intro x hx
    apply hproper.vertices_roofed
    simpa only [C.eventualRelationBlueprint_vertexSet,
      C.realRelationBlueprint_vertexSet] using hx
  covers_source := by
    intro x hx
    rcases hproper.covers_source hx with hxroot | hxreference
    · exact Or.inl (C.eventualInitial_subset_realInitial hxroot)
    · exact Or.inr (C.eventualRetainedReference_eq_realRetainedReference T ▸ hxreference)
  vertices_closed := by
    intro x hx
    apply hproper.vertices_closed
    simpa only [C.eventualRelationBlueprint_vertexSet,
      C.realRelationBlueprint_vertexSet] using hx
  card_paths := by
    apply C.realRelationBlueprint_card_paths_le
    rw [← C.eventualRelationBlueprint_vertexSet]
    exact C.eventualRelationBlueprint.mk_vertexSet_le_of_mk_paths_le
      hkappa hproper.card_paths
  infinitely_many_strong := C.realRelationBlueprint_infinitelyManyStrong
    hstrong hGamma hBtarget
  terminals_popular := by
    intro x hx
    apply Or.inl
    apply Or.inl
    apply hB
    refine ⟨C.realRelationBlueprint_terminals_subset_target hcompleted hx, ?_⟩
    rw [← C.realRelationBlueprint_vertexSet]
    exact (mem_familyGraph_terminals_of_mem_terminalSet hx).1

/-- At the final fair real limit, stability is an immediate consequence
of the carrier-local target geometry. -/
theorem realRelationBlueprint_stable
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (T : Set V)
    (hcompleted : ∀ i x, x ∈ (C.stage i).realPart.terminals →
      ∃ j, x ∈ (C.stage j).completedRealVertices B)
    (hB : B ∩ C.realVertexLimit ⊆ persistent) :
    C.realRelationBlueprint.Stable T persistent := by
  rintro x ⟨hx, _⟩
  apply hB
  refine ⟨C.realRelationBlueprint_terminals_subset_target hcompleted hx, ?_⟩
  rw [← C.realRelationBlueprint_vertexSet]
  exact (mem_familyGraph_terminals_of_mem_terminalSet hx).1

#print axioms eventualInitial_subset_realInitial
#print axioms realRelationBlueprint_isLinkageBlueprint
#print axioms realRelationBlueprint_stable

end IndexedRealExtensionChain
end LinkageBlueprint
end Blueprint
end Erdos599
