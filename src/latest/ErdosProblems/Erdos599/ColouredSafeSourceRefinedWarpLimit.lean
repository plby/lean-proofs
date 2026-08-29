/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeSourceRefinedLimit
import ErdosProblems.Erdos599.RayCompatibleRelationDecomposition

/-!
# Exact native relation-limit warp with old-slice source coverage

Source-anchored predecessor refinement rules out reverse rays. The actual
eventual relation can therefore be decomposed without losing any carrier
vertices. Increasing initial sets and source coverage at every old slice
are retained. This is not yet a proper-limit linkage blueprint: its strong
ray condition and new-slice boundary obligations remain separate.
-/

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph.RealStageChain

open Set Cardinal DirectedPath Alternating ColouredSafeLocalTransactionRealLedger

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {I : Type v} [LinearOrder I] {frontier : I → Set V}

theorem eventualEdges_adj (C : RealStageChain Gamma Y kappa I frontier) :
    C.eventualEdges ⊆ {e | (imaginaryWeb Y kappa).graph.Adj e.1 e.2} := by
  rintro e ⟨i, hi⟩
  exact familyEdges_subset_adj (C.stage i) (hi i le_rfl)

theorem eventualEdges_endpoints (C : RealStageChain Gamma Y kappa I frontier) :
    ∀ e ∈ C.eventualEdges, e.1 ∈ C.vertexUnion ∧ e.2 ∈ C.vertexUnion := by
  rintro e ⟨i, hi⟩
  have hends := familyEdges_subset_vertexSet_prod (C.stage i) (hi i le_rfl)
  exact ⟨C.stage_vertices_subset i hends.1, C.stage_vertices_subset i hends.2⟩

/-- Realizing the exact union carrier, including vertices that become
isolated, requires no fairness or completion premise. -/
theorem exists_eventualWarp
    (C : RealStageChain Gamma Y kappa I frontier)
    (hrefine : ∀ {i j}, i ≤ j → SourcePredecessorRefines (C.stage i) (C.stage j)) :
    ∃ U : Set (imaginaryWeb Y kappa).DPath,
      (imaginaryWeb Y kappa).IsWarp U ∧
      (imaginaryWeb Y kappa).vertexSet U = C.vertexUnion ∧
      familyEdges U = C.eventualEdges := by
  classical
  let incident : Set V := {x | HasIncoming C.eventualEdges x ∨ HasOutgoing C.eventualEdges x}
  let isolated : Set V := C.vertexUnion \ incident
  have hI : ∀ x ∈ isolated, ∀ y,
      (x, y) ∉ C.eventualEdges ∧ (y, x) ∉ C.eventualEdges := by
    intro x hx y
    exact ⟨fun h ↦ hx.2 (Or.inr ⟨y, h⟩), fun h ↦ hx.2 (Or.inl ⟨y, h⟩)⟩
  obtain ⟨U, hU, hUE, hUI⟩ :=
    RayCompatibleRelationDecomposition.exists_warp_realizing_biUnique_with_isolated
      (imaginaryWeb Y kappa) C.eventualEdges isolated C.eventualEdges_adj
      C.eventualEdges_biUnique C.eventualEdges_not_containsDirectedCycle
      (C.eventualEdges_not_containsReverseDirectedRay hrefine) hI
  have hincident : incident ⊆ C.vertexUnion := by
    rintro x (⟨y, hyx⟩ | ⟨y, hxy⟩)
    · exact (C.eventualEdges_endpoints _ hyx).2
    · exact (C.eventualEdges_endpoints _ hxy).1
  refine ⟨U, hU, ?_, hUE⟩
  rw [TerminalContactSwitch.vertexSet_eq_isolated_union_incident_anyWarp hU, hUI, hUE]
  apply Set.Subset.antisymm
  · exact Set.union_subset Set.sdiff_subset hincident
  · intro x hx
    by_cases hi : x ∈ incident
    · exact Or.inr hi
    · exact Or.inl ⟨hx, hi⟩

theorem coversSource_of_exact_eventualWarp
    (C : RealStageChain Gamma Y kappa I frontier) (hY : Gamma.IsWarp Y)
    {U : Set (imaginaryWeb Y kappa).DPath}
    (hU : (imaginaryWeb Y kappa).IsWarp U)
    (hUV : (imaginaryWeb Y kappa).vertexSet U = C.vertexUnion)
    (hUE : familyEdges U = C.eventualEdges) (i : I) :
    CoversSource U (frontier i) := by
  intro a ha
  by_cases haV : a ∈ C.vertexUnion
  · left
    rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hU,
      hUV, hUE]
    exact ⟨haV, C.eventualEdges_source_no_incoming ha⟩
  · right
    rcases C.covers_source i ha with hinitial | hreference
    · exact False.elim (haV (C.stage_vertices_subset i
        (initialSet_subset_vertexSet (C.stage i) hinitial)))
    · obtain ⟨p, hp, hpa⟩ := hreference
      refine ⟨p, ⟨hp.1, ?_⟩, hpa⟩
      rintro ⟨_hpY, x, hxp, hxU⟩
      have haUnion := C.source_mem_vertexUnion_of_reference_meets hY hp.1.1
        (hpa ▸ ha) ⟨x, hxp, hUV ▸ hxU⟩
      exact haV (hpa ▸ haUnion)

theorem initials_subset_of_exact_eventualWarp
    (C : RealStageChain Gamma Y kappa I frontier)
    (hI : Monotone fun i ↦ (imaginaryWeb Y kappa).initialSet (C.stage i))
    {U : Set (imaginaryWeb Y kappa).DPath}
    (hU : (imaginaryWeb Y kappa).IsWarp U)
    (hUV : (imaginaryWeb Y kappa).vertexSet U = C.vertexUnion)
    (hUE : familyEdges U = C.eventualEdges) (i : I) :
    (imaginaryWeb Y kappa).initialSet (C.stage i) ⊆
      (imaginaryWeb Y kappa).initialSet U := by
  intro x hxi
  rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hU,
    hUV, hUE]
  refine ⟨C.stage_vertices_subset i (initialSet_subset_vertexSet (C.stage i) hxi), ?_⟩
  rintro ⟨y, j, hj⟩
  have hxmax : x ∈ (imaginaryWeb Y kappa).initialSet (C.stage (max i j)) :=
    hI (le_max_left i j) hxi
  rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
    (C.warp (max i j))] at hxmax
  exact hxmax.2 ⟨y, hj _ (le_max_right _ _)⟩

/-- The simultaneous exact edge/carrier and old-boundary certificates.
No assertion about the strong edges of new forward rays is included. -/
theorem exists_eventualWarp_with_oldCoverage
    (C : RealStageChain Gamma Y kappa I frontier) (hY : Gamma.IsWarp Y)
    (hrefine : ∀ {i j}, i ≤ j → SourcePredecessorRefines (C.stage i) (C.stage j))
    (hI : Monotone fun i ↦ (imaginaryWeb Y kappa).initialSet (C.stage i)) :
    ∃ U : Set (imaginaryWeb Y kappa).DPath,
      (imaginaryWeb Y kappa).IsWarp U ∧
      (imaginaryWeb Y kappa).vertexSet U = C.vertexUnion ∧
      familyEdges U = C.eventualEdges ∧
      (∀ i, (imaginaryWeb Y kappa).initialSet (C.stage i) ⊆
        (imaginaryWeb Y kappa).initialSet U) ∧
      ∀ i, CoversSource U (frontier i) := by
  obtain ⟨U, hU, hUV, hUE⟩ := C.exists_eventualWarp hrefine
  exact ⟨U, hU, hUV, hUE,
    C.initials_subset_of_exact_eventualWarp hI hU hUV hUE,
    C.coversSource_of_exact_eventualWarp hY hU hUV hUE⟩

#print axioms exists_eventualWarp
#print axioms coversSource_of_exact_eventualWarp
#print axioms initials_subset_of_exact_eventualWarp
#print axioms exists_eventualWarp_with_oldCoverage

end Erdos599.Blueprint.ColouredSafeShortcutGraph.RealStageChain
