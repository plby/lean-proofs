/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleFiniteModification
import ErdosProblems.Erdos599.ReducingBoundary

/-!
# Finite relational reducing switches

A finite modification of a finite-character warp has finite weak
components.  If the modified relation is locally biunique, its components
therefore split into finite paths and directed cycles.  Discarding the cycle
components preserves edge balance and hence preserves the exact reducing
boundary.

Unlike the alternating-path realization theorem, this construction needs no
interval-convexity hypothesis.
-/

namespace Erdos599
namespace Alternating
namespace SwitchingCore
namespace RelationalReduction

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Discarding the cycle components of a cyclowarp preserves edge balance at
every vertex, not only its incoming and outgoing boundary sets. -/
theorem Cyclowarp.edgeBalance_pathPart_eq_edges
    (C : Cyclowarp Gamma) (x : V) :
    edgeBalance (familyEdges C.pathPart) x = edgeBalance C.edges x := by
  classical
  have hout := Set.ext_iff.mp C.outgoingBoundary_edges_eq_pathPart x
  have hin := Set.ext_iff.mp C.incomingBoundary_edges_eq_pathPart x
  change
    (HasOutgoing C.edges x ∧ ¬ HasIncoming C.edges x ↔
      HasOutgoing (familyEdges C.pathPart) x ∧
        ¬ HasIncoming (familyEdges C.pathPart) x) at hout
  change
    (HasIncoming C.edges x ∧ ¬ HasOutgoing C.edges x ↔
      HasIncoming (familyEdges C.pathPart) x ∧
        ¬ HasOutgoing (familyEdges C.pathPart) x) at hin
  by_cases hpo : HasOutgoing (familyEdges C.pathPart) x <;>
    by_cases hpi : HasIncoming (familyEdges C.pathPart) x <;>
    by_cases heo : HasOutgoing C.edges x <;>
    by_cases hei : HasIncoming C.edges x <;>
    simp [edgeBalance, propInt, hpo, hpi, heo, hei] at hout hin ⊢

/-- A finite relational switch with the reducing balance has an honest
finite-character warp realization after its directed-cycle components are
discarded.  The path edges need only be a subset of the switched relation;
their edge balance, isolated vertices, and two frontiers are exact. -/
theorem exists_finiteWarp_reducing_of_finiteRelationalSwitch
    {Z : Set Gamma.DPath} {R F E : Set (V × V)}
    (hZ : Gamma.IsWarp Z) (hZfinite : Gamma.HasFiniteCharacter Z)
    (hR : R ⊆ familyEdges Z) (hRfinite : R.Finite)
    (hFfinite : F.Finite)
    (hFgraph : F ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hFdisj : Disjoint F (familyEdges Z))
    (hE : E = (familyEdges Z \ R) ∪ F)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hiso : ∀ x ∈ isolatedVertices Z, ∀ y,
      (x, y) ∉ E ∧ (y, x) ∉ E)
    {u v : V}
    (hu : u ∈ Gamma.initialSet Z) (huNonisolated : u ∉ isolatedVertices Z)
    (hv : v ∈ Gamma.terminalFrontier Z)
    (hvNonisolated : v ∉ isolatedVertices Z)
    (hdelta : ∀ x, edgeBalance F x - edgeBalance R x =
      propInt (x = v) - propInt (x = u)) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U ⊆ E ∧
      isolatedVertices U = isolatedVertices Z ∧
      (∀ x, edgeBalance (familyEdges U) x = edgeBalance E x) ∧
      Gamma.initialSet U = Gamma.initialSet Z \ {u} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Z \ {v} := by
  have hEgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
    rw [hE]
    rintro e (he | he)
    · exact familyEdges_subset_adj Z he.1
    · exact hFgraph he
  have hfinite : ∀ c : RelationComponents.Component E,
      (RelationComponents.componentSupport E c).Finite := by
    rw [hE]
    exact Gamma.finite_componentSupports_of_finiteModification_familyEdges
      hZ hZfinite hRfinite hFfinite
  obtain ⟨C, hCEdges, hCIso, hCfinite⟩ :=
    RelationComponents.exists_cyclowarp_of_finite_componentSupports
      Gamma E (isolatedVertices Z) hEgraph
      (fun {_ _ _} h₁ h₂ ↦ hunique.2 h₁ h₂)
      (fun {_ _ _} h₁ h₂ ↦ hunique.1 h₁ h₂)
      hfinite hiso
  have hpathEdges : familyEdges C.pathPart ⊆ E := by
    intro e he
    rw [← hCEdges]
    exact Or.inl he
  have hbalance : ∀ x, edgeBalance E x =
      edgeBalance (familyEdges Z) x +
        propInt (x = v) - propInt (x = u) := by
    intro x
    have hunique' : Relator.BiUnique (fun a b ↦
        (a, b) ∈ (familyEdges Z \ R) ∪ F) := by
      rw [← hE]
      exact hunique
    rw [hE, edgeBalance_sdiff_union_eq_add_sub hR
      (fun _ _ _ h₁ h₂ ↦ familyEdges_out_unique hZ h₁ h₂)
      (fun _ _ _ h₁ h₂ ↦ familyEdges_in_unique hZ h₁ h₂)
      hunique'.2 hunique'.1
      (hFdisj.symm.mono_left Set.sdiff_subset)]
    have hd := hdelta x
    omega
  have huBalance : edgeBalance (familyEdges Z) u = 1 :=
    (mem_initialSet_iff_isolated_or_edgeBalance_eq_one hZ hZfinite).1 hu
      |>.resolve_left huNonisolated
  have hvBalance : edgeBalance (familyEdges Z) v = -1 :=
    (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
      hZ hZfinite).1 hv |>.resolve_left hvNonisolated
  have huv : u ≠ v := by
    intro huv
    subst v
    omega
  have hvu : v ≠ u := huv.symm
  have hinitial : Gamma.initialSet C.pathPart =
      Gamma.initialSet Z \ {u} := by
    ext x
    rw [C.mem_initialSet_pathPart_iff_isolated_or_edgeBalance_eq_one hCfinite]
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one hZ hZfinite,
      hCIso, hCEdges, hbalance]
    by_cases hxv : x = v
    · subst x
      simp [propInt, hvNonisolated, hvBalance, hvu]
    by_cases hxu : x = u
    · subst x
      simp [propInt, huNonisolated, huBalance, huv]
    simp [propInt, hxv, hxu]
  have hterminal : Gamma.terminalFrontier C.pathPart =
      Gamma.terminalFrontier Z \ {v} := by
    ext x
    rw [C.mem_terminalFrontier_pathPart_iff_isolated_or_edgeBalance_eq_neg_one
      hCfinite]
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
      hZ hZfinite, hCIso, hCEdges, hbalance]
    by_cases hxv : x = v
    · subst x
      simp [propInt, hvNonisolated, hvBalance, hvu]
    by_cases hxu : x = u
    · subst x
      simp [propInt, huNonisolated, huBalance, huv]
    simp [propInt, hxv, hxu]
  refine ⟨C.pathPart, C.pathPart_isWarp, hCfinite, hpathEdges, ?_, ?_,
    hinitial, hterminal⟩
  · exact hCIso
  · intro x
    rw [RelationalReduction.Cyclowarp.edgeBalance_pathPart_eq_edges C,
      hCEdges]

#print axioms Cyclowarp.edgeBalance_pathPart_eq_edges
#print axioms exists_finiteWarp_reducing_of_finiteRelationalSwitch

end RelationalReduction
end SwitchingCore
end Alternating
end Erdos599
