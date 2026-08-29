/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RayCompatibleRelationDecomposition
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Restricting a finite-character warp to a finite vertex carrier

Intersecting every old member with a vertex set can split it into several
finite intervals.  It is cleaner to realize the induced edge relation and
to add precisely the retained vertices not incident with that relation as
singleton paths.  This gives exact edge and vertex carriers and preserves
old initial vertices lying in the retained carrier.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.FiniteWarpCarrierRestriction

open DirectedPath RelationDecomposition

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A finite carrier induces a genuine finite-character warp with exactly
the old edges whose two endpoints remain in the carrier.  Old initial
vertices retained by the carrier remain initial in the induced warp. -/
theorem exists_restriction
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    (hWfinite : Gamma.HasFiniteCharacter W)
    (C : Set V) (hCfinite : C.Finite) :
    ∃ WC : Set Gamma.DPath,
      Gamma.IsWarp WC ∧
      Gamma.HasFiniteCharacter WC ∧
      Gamma.vertexSet WC = Gamma.vertexSet W ∩ C ∧
      familyEdges WC = familyEdges W ∩ (C ×ˢ C) ∧
      Gamma.initialSet W ∩ C ⊆ Gamma.initialSet WC := by
  classical
  let E : Set (V × V) := familyEdges W ∩ (C ×ˢ C)
  let carrier : Set V := Gamma.vertexSet W ∩ C
  let incident : Set V :=
    {x | HasIncoming E x ∨ HasOutgoing E x}
  let I : Set V := carrier \ incident
  have hEsub : E ⊆ familyEdges W := fun _ h ↦ h.1
  have hEgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
    hEsub.trans (familyEdges_subset_adj W)
  have hEbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    exact ⟨fun _ _ _ h₁ h₂ ↦
        (IsWarp.familyEdges_biUnique hW).1 h₁.1 h₂.1,
      fun _ _ _ h₁ h₂ ↦
        (IsWarp.familyEdges_biUnique hW).2 h₁.1 h₂.1⟩
  have hEcycle : ¬ ContainsDirectedCycle E := by
    rintro ⟨D, hD⟩
    exact SwitchingCore.familyEdges_not_containsDirectedCycle hW hWfinite
      ⟨D, hD.trans hEsub⟩
  have hEreverse : ¬ ContainsReverseDirectedRay E := by
    rintro ⟨R, hR⟩
    exact SwitchingCore.familyEdges_not_containsReverseDirectedRay hW hWfinite
      ⟨R, fun n ↦ hEsub (hR n)⟩
  have hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E := by
    intro x hx y
    constructor
    · intro hxy
      exact hx.2 (Or.inr ⟨y, hxy⟩)
    · intro hyx
      exact hx.2 (Or.inl ⟨y, hyx⟩)
  obtain ⟨WC, hWC, hWCE, hWCI⟩ :=
    RayCompatibleRelationDecomposition.exists_warp_realizing_biUnique_with_isolated
      Gamma E I hEgraph hEbi hEcycle hEreverse hI
  have hincident_sub : incident ⊆ carrier := by
    intro x hx
    rcases hx with ⟨y, hyx⟩ | ⟨y, hxy⟩
    · have hyxW : (y, x) ∈ familyEdges W := hEsub hyx
      have hxW := (familyEdges_subset_vertexSet_prod W hyxW).2
      exact ⟨hxW, hyx.2.2⟩
    · have hxyW : (x, y) ∈ familyEdges W := hEsub hxy
      have hxW := (familyEdges_subset_vertexSet_prod W hxyW).1
      exact ⟨hxW, hxy.2.1⟩
  have hvertex : Gamma.vertexSet WC = carrier := by
    rw [TerminalContactSwitch.vertexSet_eq_isolated_union_incident_anyWarp hWC,
      hWCI, hWCE]
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with hx | hx
      · exact hx.1
      · exact hincident_sub hx
    · intro x hx
      by_cases hxi : x ∈ incident
      · exact Or.inr hxi
      · exact Or.inl ⟨hx, hxi⟩
  have hcarrierFinite : carrier.Finite :=
    hCfinite.subset Set.inter_subset_right
  have hWCfinite : Gamma.HasFiniteCharacter WC := by
    intro p hp
    rcases p with p | r
    · exact ⟨p, rfl⟩
    · have hrange : Set.range r ⊆ carrier := by
        rintro x ⟨n, rfl⟩
        rw [← hvertex]
        exact ⟨.inr r, hp, ⟨n, rfl⟩⟩
      exact False.elim (hcarrierFinite.not_infinite
        ((Set.infinite_range_of_injective r.injective).mono hrange))
  have hinitial : Gamma.initialSet W ∩ C ⊆ Gamma.initialSet WC := by
    intro x hx
    have hxOld := hx.1
    rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
      hW] at hxOld
    rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
      hWC]
    constructor
    · rw [hvertex]
      exact ⟨hxOld.1, hx.2⟩
    · rintro ⟨y, hyx⟩
      rw [hWCE] at hyx
      exact hxOld.2 ⟨y, hyx.1⟩
  exact ⟨WC, hWC, hWCfinite, by simpa only [carrier] using hvertex,
    by simpa only [E] using hWCE, hinitial⟩

#print axioms exists_restriction

end Erdos599.Alternating.FiniteWarpCarrierRestriction
