/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AugmentedAccountedChain
import ErdosProblems.Erdos599.RayCompatibleRelationDecomposition

/-!
# The exact eventual warp of an accounted augmented history

The existing relation decomposition realizes every vertex of the union,
including newly isolated vertices. Initials, finite real paths, predecessor
refinement and full target accounting pass to that same exact output.
-/

namespace Erdos599.AugmentedAccountedChain

open Set DirectedPath Alternating ColouredSafeLocalTransactionRealLedger
open ColouredSafeAugmentedRealReach

universe u v

variable {V : Type u} {Gamma D : DWeb V} {I : Type v} [LinearOrder I]

theorem exists_eventualWarp (C : AugmentedAccountedChain Gamma D I) :
    ∃ U : Set D.DPath, D.IsWarp U ∧ D.vertexSet U = C.vertexUnion ∧
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
      D C.eventualEdges isolated C.eventualEdges_adj C.eventualEdges_biUnique
      C.eventualEdges_not_containsDirectedCycle C.eventualEdges_not_containsReverseDirectedRay hI
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

variable {U : Set D.DPath}

theorem initials_subset_of_exact_eventualWarp (C : AugmentedAccountedChain Gamma D I)
    (hU : D.IsWarp U) (hUV : D.vertexSet U = C.vertexUnion)
    (hUE : familyEdges U = C.eventualEdges) (i : I) :
    D.initialSet (C.stage i) ⊆ D.initialSet U := by
  intro x hxi
  rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hU, hUV, hUE]
  refine ⟨C.stage_vertices_subset i (initialSet_subset_vertexSet (C.stage i) hxi), ?_⟩
  rintro ⟨y, j, hj⟩
  have hxmax : x ∈ D.initialSet (C.stage (max i j)) := C.initials_mono (le_max_left i j) hxi
  rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
    (C.warp (max i j))] at hxmax
  exact hxmax.2 ⟨y, hj _ (le_max_right _ _)⟩

theorem realReach_exact_eventualWarp (C : AugmentedAccountedChain Gamma D I)
    (hUV : D.vertexSet U = C.vertexUnion) (hUE : familyEdges U = C.eventualEdges)
    {i : I} {a b : V} (h : RealReach Gamma D (C.stage i) a b) : RealReach Gamma D U a b := by
  apply h.mono
  · rw [hUV]
    exact C.stage_vertices_subset i
  · intro e he
    exact ⟨hUE.symm ▸ C.stage_realEdges_subset i he, he.2⟩

theorem sourcePredecessorRefines_eventualWarp (C : AugmentedAccountedChain Gamma D I)
    (hUV : D.vertexSet U = C.vertexUnion) (hUE : familyEdges U = C.eventualEdges) (i : I) :
    SourcePredecessorRefines Gamma D (C.stage i) U := by
  intro x y hx hyx
  obtain ⟨j0, hj0⟩ := hUE ▸ hyx
  rcases C.predecessor (le_max_left i j0) hx
      (hj0 (max i j0) (le_max_right _ _)) with hold | ⟨z, hz, hzx⟩ | ⟨a, ha, hax⟩
  · exact Or.inl hold
  · exact Or.inr (Or.inl ⟨z, hz, C.realReach_exact_eventualWarp hUV hUE hzx⟩)
  · exact Or.inr (Or.inr ⟨a, ha, C.realReach_exact_eventualWarp hUV hUE hax⟩)

theorem fullAccount_eventualWarp (C : AugmentedAccountedChain Gamma D I)
    (hU : D.IsWarp U) (hUV : D.vertexSet U = C.vertexUnion)
    (hUE : familyEdges U = C.eventualEdges) (i : I) :
    FullAccount Gamma D (C.stage i) U Gamma.target := by
  classical
  intro x hx
  by_cases hdone : ∃ j, RealReaches Gamma D (C.stage j) x Gamma.target
  · obtain ⟨j, b, hb, hxb⟩ := hdone
    exact Or.inr (Or.inr ⟨b, hb, C.realReach_exact_eventualWarp hUV hUE hxb⟩)
  have hnotDone : ∀ j, ¬RealReaches Gamma D (C.stage j) x Gamma.target := fun j hj ↦ hdone ⟨j, hj⟩
  by_cases hxT : x ∈ D.terminalFrontier (C.stage i)
  · left
    refine ⟨hxT, ?_⟩
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hU,
      hUV, hUE]
    refine ⟨C.stage_vertices_subset i hx, ?_⟩
    rintro ⟨y, j0, hj0⟩
    let j := max i j0
    have hjEdge := hj0 j (le_max_right _ _)
    rcases C.account (le_max_left i j0) x hx with hterm | ⟨z, hzi, _⟩ | hcompleted
    · have hno := hterm.2
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
        (C.warp j)] at hno
      exact hno.2 ⟨y, hjEdge⟩
    · have hno := hxT
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
        (C.warp i)] at hno
      exact hno.2 ⟨z, hzi⟩
    · exact hnotDone j hcompleted
  · have hout : HasOutgoing (familyEdges (C.stage i)) x := by
      by_contra hno
      apply hxT
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp (C.warp i)]
      exact ⟨hx, hno⟩
    obtain ⟨y, hxy⟩ := hout
    refine Or.inr (Or.inl ⟨y, hxy, ?_⟩)
    rw [hUE]
    refine ⟨i, ?_⟩
    intro j hij
    rcases C.account hij x hx with hterm | ⟨z, hzi, hzj⟩ | hcompleted
    · exact False.elim (hxT hterm.1)
    · have hzy := (IsWarp.familyEdges_biUnique (C.warp i)).2 hzi hxy
      exact hzy ▸ hzj
    · exact False.elim (hnotDone j hcompleted)

#print axioms exists_eventualWarp
#print axioms initials_subset_of_exact_eventualWarp
#print axioms realReach_exact_eventualWarp
#print axioms sourcePredecessorRefines_eventualWarp
#print axioms fullAccount_eventualWarp

end Erdos599.AugmentedAccountedChain
