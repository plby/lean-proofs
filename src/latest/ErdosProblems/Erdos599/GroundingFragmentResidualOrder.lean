/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedDecode
import ErdosProblems.Erdos599.GroundingFragmentUniqueness

/-!
# Residual ladder edges preserve deleted fragments and their order

The base relation in the simultaneous grounding switch consists of ladder
edges which survive deletion of the represented cut edges.  Maximality of a
deleted fragment implies that such an edge cannot leave the fragment through
its head.  Moreover the edge advances, rather than reverses, the intrinsic
order of every concrete representation of that fragment.

These are the local facts needed by the blocking-point reachability argument
in Assertion 8.22.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFragmentResidualOrder

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (_L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- The endpoints of an edge of a directed finite path or ray are distinct. -/
theorem ne_of_mem_dpath_edgeSet {P : Gamma.DPath} {x y : V}
    (hxy : (x, y) ∈ P.edgeSet) : x ≠ y := by
  cases P with
  | inl p =>
      obtain ⟨n, hn, hnx, hny⟩ :=
        DirectedPath.Walk.exists_adjacent_getElem_of_mem_edgeSet p.walk hxy
      intro h
      have heq : p.walk.support[n] = p.walk.support[n + 1] :=
        hnx.trans (h.trans hny.symm)
      have := p.isPath.getElem_inj_iff.mp heq
      omega
  | inr r =>
      obtain ⟨n, hn⟩ := hxy
      intro hxy
      apply Nat.ne_of_lt (Nat.lt_succ_self n)
      apply r.injective
      exact (congrArg Prod.fst hn).symm.trans <|
        hxy.trans (congrArg Prod.snd hn)

/-- One surviving parent edge is a witness of surviving connectivity between
its endpoints. -/
theorem survivingConnected_of_mem_parent_edge
    (L : Input Gamma I) (C : Set (LV L)) (parent : Gamma.DPath)
    {x y : V} (hxy : (x, y) ∈ parent.edgeSet)
    (hnotCE : (x, y) ∉ GroundingCut.CE L C) :
    GroundingCut.SurvivingConnected L C parent x y := by
  have hAdj : Gamma.graph.Adj x y := parent.edgeSet_subset_adj hxy
  have hne : x ≠ y := ne_of_mem_dpath_edgeSet hxy
  let q : FinitePath Gamma.graph :=
    { start := x
      finish := y
      walk := .cons hAdj .nil
      isPath := by simp [Walk.IsPath, Walk.support, hne] }
  refine ⟨q, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro z hz
    have hzxy : z = x ∨ z = y := by
      simpa [q, FinitePath.support, Walk.support] using hz
    rcases hzxy with rfl | rfl
    · exact (parent.edgeSet_subset_support_prod hxy).1
    · exact (parent.edgeSet_subset_support_prod hxy).2
  · intro e he
    have heq : e = (x, y) := by
      simpa [q, FinitePath.edgeSet, Walk.edgeSet] using he
    simpa [heq] using hxy
  · rw [Set.disjoint_left]
    intro e he hce
    have heq : e = (x, y) := by
      simpa [q, FinitePath.edgeSet, Walk.edgeSet] using he
    apply hnotCE
    exact heq ▸ hce

/-- A surviving ladder edge whose tail lies in a maximal deleted fragment
has its head in the same fragment. -/
theorem head_mem_fragment_of_mem_surviving_edge
    {L : Input Gamma I} {C : Set (LV L)} {P : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L C) {x y : V}
    (hx : x ∈ P.path.support) (hxy : (x, y) ∈ L.familyEdges)
    (hnotCE : (x, y) ∉ GroundingCut.CE L C) :
    y ∈ P.path.support := by
  obtain ⟨Y, hYLadder, hxyY⟩ := hxy
  have hparent : P.parent = Y :=
    Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
      P.parent_mem hYLadder (P.support_subset hx)
      (Y.edgeSet_subset_support_prod hxyY).1
  have hix : GroundingCut.SurvivingConnected L C P.parent
      P.path.initial x :=
    GroundingFragmentRelation.survivingConnected_of_mem_fragment
      hP P.path.initial_mem_support hx
  have hxyConnected : GroundingCut.SurvivingConnected L C P.parent x y := by
    rw [hparent]
    exact survivingConnected_of_mem_parent_edge L C Y hxyY hnotCE
  rw [hP.2]
  exact ⟨hparent ▸ (Y.edgeSet_subset_support_prod hxyY).2,
    GroundingFragmentRelation.survivingConnected_trans
      L C P.parent hix hxyConnected⟩

/-- A surviving ladder edge advances the concrete order of the maximal
deleted fragment containing its tail. -/
theorem beforeEq_of_mem_surviving_edge
    {L : Input Gamma I} {C : Set (LV L)} {P : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L C) {x y : V}
    (hx : x ∈ P.path.support) (hxy : (x, y) ∈ L.familyEdges)
    (hnotCE : (x, y) ∉ GroundingCut.CE L C) :
    GroundingCut.BeforeEq P.path x y := by
  have hy : y ∈ P.path.support :=
    head_mem_fragment_of_mem_surviving_edge hP hx hxy hnotCE
  rcases GroundingCut.beforeEq_total hx hy with hxyPath | hyxPath
  · exact hxyPath
  · exfalso
    obtain ⟨Y, hYLadder, hxyY⟩ := hxy
    have hparent : P.parent = Y :=
      Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
        P.parent_mem hYLadder (P.support_subset hx)
        (Y.edgeSet_subset_support_prod hxyY).1
    have hxyParent : GroundingCut.BeforeEq P.parent x y := by
      rw [hparent]
      exact GroundingErasedDecode.GroundingCut.beforeEq_of_mem_edgeSet hxyY
    have hyxParent : GroundingCut.BeforeEq P.parent y x :=
      GroundingFragmentUniqueness.beforeEq_parent P hyxPath
    exact ne_of_mem_dpath_edgeSet hxyY
      (GroundingCutDecoder.beforeEq_antisymm hxyParent hyxParent)

/-- Specialized form for an edge of the CE-residual ladder relation. -/
theorem beforeEq_of_mem_residualLadderEdges
    {J : Type u} {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma J}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) {P : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L S.cut) {x y : V}
    (hx : x ∈ P.path.support)
    (hxy : (x, y) ∈ GroundingErasedDecode.residualLadderEdges U S) :
    GroundingCut.BeforeEq P.path x y :=
  beforeEq_of_mem_surviving_edge hP hx hxy.1 hxy.2

/-- Transitivity of the intrinsic order on a directed finite path or ray. -/
theorem beforeEq_trans {P : Gamma.DPath} {x y z : V}
    (hxy : GroundingCut.BeforeEq P x y)
    (hyz : GroundingCut.BeforeEq P y z) :
    GroundingCut.BeforeEq P x z := by
  rcases hxy with ⟨m, n, hmx, hny, hmn⟩
  rcases hyz with ⟨p, q, hpy, hqz, hpq⟩
  have hnp : n = p :=
    GroundingCutDecoder.occursAt_index_injective hny hpy
  exact ⟨m, q, hmx, hqz, by omega⟩

/-- A chain consisting only of residual ladder edges cannot leave a maximal
deleted fragment and is monotone in that fragment's intrinsic order. -/
theorem mem_and_beforeEq_of_reflTransGen_residualLadderEdges
    {J : Type u} {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma J}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) {P : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L S.cut) {x y : V}
    (hx : x ∈ P.path.support)
    (hxy : Relation.ReflTransGen
      (fun a b ↦ (a, b) ∈ GroundingErasedDecode.residualLadderEdges U S)
      x y) :
    y ∈ P.path.support ∧ GroundingCut.BeforeEq P.path x y := by
  induction hxy using Relation.ReflTransGen.trans_induction_on with
  | refl => exact ⟨hx, GroundingCut.beforeEq_refl hx⟩
  | single hab =>
      exact ⟨
        head_mem_fragment_of_mem_surviving_edge hP hx hab.1 hab.2,
        beforeEq_of_mem_residualLadderEdges U S hP hx hab⟩
  | trans hab hbc ihab ihbc =>
      obtain ⟨hb, hxab⟩ := ihab hx
      obtain ⟨hc, hxbc⟩ := ihbc hb
      exact ⟨hc, beforeEq_trans hxab hxbc⟩

/-- Order-only projection of
`mem_and_beforeEq_of_reflTransGen_residualLadderEdges`. -/
theorem beforeEq_of_reflTransGen_residualLadderEdges
    {J : Type u} {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma J}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) {P : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L S.cut) {x y : V}
    (hx : x ∈ P.path.support)
    (hxy : Relation.ReflTransGen
      (fun a b ↦ (a, b) ∈ GroundingErasedDecode.residualLadderEdges U S)
      x y) :
    GroundingCut.BeforeEq P.path x y :=
  (mem_and_beforeEq_of_reflTransGen_residualLadderEdges
    U S hP hx hxy).2

end GroundingFragmentResidualOrder
end Erdos599
