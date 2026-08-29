/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930PriorIntervalClosure
import ErdosProblems.Erdos599.HalfwayInsideFragmentUnion

/-!
# The local old-slice branch of Assertion 9.30

A scheduled real terminal which already lies on the current frontier needs
no hammock replacement.  If it still has an outgoing blueprint edge, that
edge is necessarily non-real and the canonical one-edge cut makes the
scheduled vertex a whole-blueprint terminal.  This file proves the full
9.32 accounting for that cut, including the isolated scheduled vertex.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace IsCutAt

variable {W cut : LinkageBlueprint Gamma Y kappa} {u : V}

theorem vertexSet_eq (h : W.IsCutAt cut u) : cut.vertexSet = W.vertexSet := by
  rcases h with ⟨_, rfl⟩ | ⟨v, hv⟩
  · rfl
  · exact hv.vertices_eq

theorem edgeSet_subset (h : W.IsCutAt cut u) : cut.edgeSet ⊆ W.edgeSet := by
  rcases h with ⟨_, rfl⟩ | ⟨v, hv⟩
  · exact Set.Subset.rfl
  · rw [hv.edges_eq]
    exact Set.sdiff_subset

/-- Every edge whose tail is not the cut vertex survives the one-edge cut. -/
theorem edge_mem_of_fst_ne (h : W.IsCutAt cut u)
    {x y : V} (hxu : x ≠ u) (hxy : (x, y) ∈ W.edgeSet) :
    (x, y) ∈ cut.edgeSet := by
  rcases h with ⟨_, rfl⟩ | ⟨v, hv⟩
  · exact hxy
  · rw [hv.edges_eq]
    refine ⟨hxy, ?_⟩
    intro heq
    exact hxu (congrArg Prod.fst heq)

/-- Cutting the outgoing non-real edge of a real terminal preserves every
real edge in both directions. -/
theorem realPart_edges_eq (h : W.IsCutAt cut u)
    (hu : u ∈ W.realPart.terminals) :
    cut.realPart.edges = W.realPart.edges := by
  apply Set.Subset.antisymm
  · rintro e ⟨heCut, heReal⟩
    exact ⟨h.edgeSet_subset heCut, heReal⟩
  · rintro ⟨x, y⟩ he
    rcases h with ⟨_, rfl⟩ | ⟨v, hv⟩
    · exact he
    · change (x, y) ∈ cut.edgeSet ∩ {e | Gamma.graph.Adj e.1 e.2}
      rw [hv.edges_eq]
      refine ⟨⟨he.1, ?_⟩, he.2⟩
      intro heq
      have hxu : x = u := congrArg Prod.fst heq
      have hyv : y = v := congrArg Prod.snd heq
      subst x
      subst y
      exact hu.2 ⟨v, he⟩

theorem realPart_extends (h : W.IsCutAt cut u)
    (hu : u ∈ W.realPart.terminals) :
    W.realPart.Extends cut.realPart := by
  refine ⟨?_, ?_⟩
  · intro x hx
    change x ∈ W.vertexSet at hx
    change x ∈ cut.vertexSet
    rw [h.vertexSet_eq]
    exact hx
  · rw [h.realPart_edges_eq hu]

theorem realTerminal_iff (h : W.IsCutAt cut u)
    (hu : u ∈ W.realPart.terminals) {x : V} :
    x ∈ cut.realPart.terminals ↔ x ∈ W.realPart.terminals := by
  rw [FamilyGraph.terminals, FamilyGraph.terminals,
    FamilyGraph.tails, FamilyGraph.tails, h.realPart_edges_eq hu,
    realPart_vertices, realPart_vertices, h.vertexSet_eq]

/-- The cut satisfies the exact old-vertex accounting of (9.32), with the
scheduled vertex accounted for by its trivial completed real path. -/
theorem realExtends_singleton (h : W.IsCutAt cut u)
    (hu : u ∈ W.realPart.terminals) :
    W.RealExtends cut {u} := by
  refine ⟨h.realPart_extends hu, ?_⟩
  intro x hxW
  by_cases hxu : x = u
  · subst x
    apply Or.inr
    let p : FinitePath Gamma.graph := FinitePath.trivial Gamma.graph u
    refine ⟨p, Set.mem_singleton u, ?_, ?_, ?_⟩
    · intro x hx
      have hxeq : x = u := by simpa [p] using hx
      subst x
      rw [realPart_vertices, h.vertexSet_eq]
      exact hu.1
    · simp [p, FinitePath.edgeSet]
    · exact p.start_mem_support
  · by_cases hxterm : x ∈ W.terminalSet
    · apply Or.inl
      apply Or.inl
      refine ⟨?_, hxterm⟩
      rw [cut.terminalSet_eq_no_outgoing]
      refine ⟨h.vertexSet_eq.symm ▸ hxW, ?_⟩
      rintro ⟨y, hxy⟩
      exact W.no_outgoing_of_mem_terminalSet hxterm
        ⟨y, h.edgeSet_subset hxy⟩
    · obtain ⟨y, hxy⟩ :=
        W.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet hxW hxterm
      exact Or.inl (Or.inr ⟨y, hxy, h.edge_mem_of_fst_ne hxu hxy⟩)

end IsCutAt

/-- Complete local Assertion 9.30 when the scheduled real terminal already
belongs to the old frontier. -/
theorem exists_continuation930_of_mem_slice
    (W : LinkageBlueprint Gamma Y kappa) {u : V} {T B : Set V}
    (hu : u ∈ W.realPart.terminals) (huT : u ∈ T) :
    ∃ cut : LinkageBlueprint Gamma Y kappa,
      Continuation930 W cut cut u u T B := by
  obtain ⟨cut, hcut⟩ := exists_isCutAt_of_mem_realPart_terminals W hu
  let p : FinitePath Gamma.graph := FinitePath.trivial Gamma.graph u
  have hpSupport : p.support ⊆ cut.realPart.vertices := by
    intro x hx
    have hxeq : x = u := by simpa [p] using hx
    subst x
    rw [realPart_vertices, hcut.vertexSet_eq]
    exact hu.1
  have hpEdges : p.edgeSet ⊆ cut.realPart.edges := by
    simp [p, FinitePath.edgeSet]
  have hlinksSingleton : cut.RealLinksTo u {u} := by
    exact ⟨p, rfl, Set.mem_singleton u, hpSupport, hpEdges⟩
  have hlinksT : cut.RealLinksTo u T := by
    exact ⟨p, rfl, huT, hpSupport, hpEdges⟩
  refine ⟨cut, {
    conclusion := ⟨hcut, ordinaryExtends_refl cut, hlinksT, ?_⟩
    links_to_endpoint := hlinksSingleton
    endpoint_mem_slice := huT
    endpoint_terminal := hcut.realTerminal_iff hu |>.2 hu
    preserves_other_terminals := ?_
    endpoint_fresh := by simp
    real_extends_to_endpoint := hcut.realExtends_singleton hu }⟩
  · intro x hx
    exact hcut.realTerminal_iff hu |>.2 hx.1
  · intro x hx
    exact hcut.realTerminal_iff hu |>.2 hx.1

/-- The fully coupled local branch: first perform the exact 9.30 cut at the
old frontier, then choose the honest old-to-new interval and close its
source-prefix row together with the identity request. -/
structure OldSlice930IntervalTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    (u : V) where
  cut : LinkageBlueprint Gamma C.selectedReference kappa
  continuation : Continuation930 W cut cut u u C.oldSlice Gamma.target
  old_mem : u ∈ C.oldSlice
  interval : OldStageIntervalTransaction C u
  closed : ClosedPrior930IntervalTransaction
    (PriorContact930Request.identity (C := C) (W := W) (u := u) old_mem) interval

/-- The local branch is unconditional from the induction hypotheses and the
public club geometry; it uses no replacement compiler or target-tail-in-roof
assumption. -/
theorem exists_oldSlice930IntervalTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent)
    (hu : u ∈ W.realPart.terminals) (huOld : u ∈ C.oldSlice)
    (hbefore : C.before ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    Nonempty (OldSlice930IntervalTransaction C W u) := by
  obtain ⟨cut, hcontinuation⟩ :=
    exists_continuation930_of_mem_slice W hu huOld
  obtain ⟨T⟩ := C.exists_oldStageIntervalTransaction hlower hext huOld
  let R : PriorContact930Request C W u :=
    PriorContact930Request.identity (C := C) (W := W) (u := u) huOld
  obtain ⟨Q⟩ := R.exists_closedIntervalTransaction T hW hbefore href
    hSafeRoof (by trivial)
  exact ⟨{
    cut := cut
    continuation := hcontinuation
    old_mem := huOld
    interval := T
    closed := Q }⟩

#print axioms exists_continuation930_of_mem_slice
#print axioms exists_oldSlice930IntervalTransaction

end LinkageBlueprint
end Blueprint
end Erdos599
