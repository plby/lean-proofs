/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFragmentResidualOrder
import ErdosProblems.Erdos599.GroundingFragmentPartition
import ErdosProblems.Erdos599.GroundingFragmentWarp
import ErdosProblems.Erdos599.LambdaRawPortIncidence

/-!
# Surviving edges belong to actual maximal fragment paths

Vertex coverage alone is insufficient for applying the intrinsic grounding
theorem. A surviving edge with tail on a maximal fragment is an edge of
that fragment, by its order and uniqueness of the parent predecessor.
-/

noncomputable section

namespace Erdos599.GroundingSurvivingEdgeFragment

open Set DirectedPath Alternating

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable (L : PopularAuxiliary.Input Gamma I)

theorem edge_mem_fragment {C : Set L.LV} (P : L.Fragment)
    (hP : P ∈ GroundingCut.fragments L C) {x y : V}
    (hx : x ∈ P.path.support) (hxy : (x, y) ∈ L.familyEdges)
    (hnot : (x, y) ∉ GroundingCut.CE L C) : (x, y) ∈ P.path.edgeSet := by
  have hy := GroundingFragmentResidualOrder.head_mem_fragment_of_mem_surviving_edge
    hP hx hxy hnot
  have horder := GroundingFragmentResidualOrder.beforeEq_of_mem_surviving_edge
    hP hx hxy hnot
  have hne : y ≠ P.path.initial := by
    intro heq
    have hyx : GroundingCut.BeforeEq P.path y x :=
      heq ▸ GroundingFragmentWarp.initial_beforeEq_of_mem hx
    have hsame := GroundingCutDecoder.beforeEq_antisymm horder hyx
    obtain ⟨Y, _hY, heY⟩ := hxy
    exact GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet heY hsame
  obtain ⟨z, hzy⟩ : ∃ z, (z, y) ∈ P.path.edgeSet := by
    cases hpath : P.path with
    | inl p =>
        exact FinitePath.exists_incoming_edge_of_mem_support_of_ne_start p
          (by simpa only [hpath, Path.support] using hy)
          (by simpa only [hpath, Path.initial] using hne)
    | inr p =>
        exact Ray.hasIncoming_edgeSet_of_mem_support_of_ne_initial p
          (by simpa only [hpath, Path.support] using hy)
          (by simpa only [hpath, Path.initial] using hne)
  have hzx : z = x := L.raw_familyEdges_biUnique.1
    ⟨P.parent, P.parent_mem, P.edges_subset hzy⟩ hxy
  exact hzx ▸ hzy

/-- Maximal surviving fragments cover every surviving reference edge. -/
theorem exists_fragment_containing_edge {C : Set L.LV} {e : V × V}
    (he : e ∈ L.familyEdges) (hnot : e ∉ GroundingCut.CE L C) :
    ∃ P : L.Fragment, P ∈ GroundingCut.fragments L C ∧ e ∈ P.path.edgeSet := by
  obtain ⟨Y, hY, heY⟩ := he
  obtain ⟨P, _hparent, hP, htail⟩ :=
    GroundingFragmentPartition.exists_fragment_containing L C hY
      (Y.edgeSet_subset_support_prod heY).1
  exact ⟨P, hP, edge_mem_fragment L P hP htail ⟨Y, hY, heY⟩ hnot⟩

#print axioms exists_fragment_containing_edge

end Erdos599.GroundingSurvivingEdgeFragment
