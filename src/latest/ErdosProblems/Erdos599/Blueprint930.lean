/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause

/-!
# The scheduled-slice form of Assertion 9.30

The continuation endpoint in `Continuation930` is required to belong to the
current slice.  Accordingly, the scheduler-facing compiler only requests a
continuation for a real terminal already scheduled in that slice.

There are two cases.  If the real terminal is also a terminal of the whole
blueprint, the cut is the blueprint itself.  Otherwise its outgoing edge is
imaginary.  Deleting exactly that edge gives the cut `W^u`, which is also
used as the continuation blueprint; this makes `u` a full terminal for the
subsequent 9.31 step.  In either case the trivial real path at `u` supplies
the required link to the slice.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A path-family terminal has no outgoing family edge.  This does not need
the endpoint-purity hypothesis used later when identifying target sets. -/
theorem mem_familyGraph_terminals_of_mem_terminalSet
    {W : LinkageBlueprint Gamma Y kappa} {x : V}
    (hx : x ∈ W.terminalSet) : x ∈ W.familyGraph.terminals := by
  rcases hx with ⟨p, hpW, hpx⟩
  have hxP : x ∈ p.support :=
    (imaginaryWeb Gamma Y kappa).terminal_mem_support hpx
  refine ⟨⟨p, hpW, hxP⟩, ?_⟩
  rintro ⟨y, hy⟩
  simp only [familyGraph, edgeSet, Set.mem_iUnion] at hy
  obtain ⟨q, hqW, hxy⟩ := hy
  have hxQ : x ∈ q.support := (q.edgeSet_subset_support_prod hxy).1
  have hpq : p = q := W.path_eq_of_mem_support hpW hqW hxP hxQ
  subst q
  rcases p with p | r
  · have hfinish : p.finish = x := by
      simpa only [DWeb.terminal?_finite, Option.some.injEq] using hpx
    subst x
    exact p.noOutgoingAtFinish y hxy
  · simp only [DWeb.terminal?_ray] at hpx
    cases hpx

private theorem real_terminal_cases
    {W : LinkageBlueprint Gamma Y kappa} {u : V}
    (hu : u ∈ W.realPart.terminals) :
    u ∈ W.terminalSet ∨
      ∃ v, (u, v) ∈ W.edgeSet ∧ IsImaginaryEdge Gamma Y kappa u v := by
  by_cases hut : u ∈ W.terminalSet
  · exact Or.inl hut
  · right
    obtain ⟨v, huv⟩ :=
      W.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet hu.1 hut
    refine ⟨v, huv, ?_⟩
    have hadj : (imaginaryGraph Gamma Y kappa).Adj u v := by
      rcases Set.mem_iUnion.1 huv with ⟨p, huv⟩
      rcases Set.mem_iUnion.1 huv with ⟨hpW, hpedge⟩
      exact p.edgeSet_subset_adj hpedge
    rcases hadj with horiginal | himaginary
    · exact False.elim <| hu.2
        ⟨v, W.mem_realPart_of_mem_edgeSet_of_original huv horiginal⟩
    · exact himaginary

/-- Deleting the unique outgoing imaginary edge makes its tail a terminal
of the cut blueprint. -/
theorem IsImaginaryEdgeDeletionAt.tail_mem_terminalSet
    {W cut : LinkageBlueprint Gamma Y kappa} {u v : V}
    (h : W.IsImaginaryEdgeDeletionAt cut u v) : u ∈ cut.terminalSet := by
  have huvertex : u ∈ cut.vertexSet := by
    rw [h.vertices_eq]
    rcases Set.mem_iUnion.1 h.edge_mem with ⟨p, he⟩
    rcases Set.mem_iUnion.1 he with ⟨hpW, hpedge⟩
    exact ⟨p, hpW, (p.edgeSet_subset_support_prod hpedge).1⟩
  by_contra huterm
  obtain ⟨w, huwcut⟩ :=
    cut.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
      huvertex huterm
  have huwcut' : (u, w) ∈ W.edgeSet \ {(u, v)} := by
    simpa only [h.edges_eq] using huwcut
  have huwW : (u, w) ∈ W.edgeSet := huwcut'.1
  have hwv : w = v :=
    Erdos599.Alternating.IsWarp.familyEdges_rightUnique W.isWarp
      huwW h.edge_mem
  exact huwcut'.2 (by simpa [hwv])

/-- At a real terminal, deleting its outgoing imaginary edge preserves all
real vertices and edges. -/
theorem IsImaginaryEdgeDeletionAt.realPart_extends_cut
    {W cut : LinkageBlueprint Gamma Y kappa} {u v : V}
    (h : W.IsImaginaryEdgeDeletionAt cut u v)
    (hu : u ∈ W.realPart.terminals) :
    W.realPart.Extends cut.realPart := by
  constructor
  · intro x hx
    simpa only [realPart_vertices, h.vertices_eq] using hx
  · rintro e ⟨heW, heD⟩
    refine ⟨?_, heD⟩
    rw [h.edges_eq]
    refine ⟨heW, ?_⟩
    intro he
    have heq : e = (u, v) := Set.mem_singleton_iff.mp he
    subst e
    exact hu.2 ⟨v, ⟨h.edge_mem, heD⟩⟩

/-- Every old real terminal survives an imaginary-edge cut. -/
theorem IsImaginaryEdgeDeletionAt.preserves_realTerminals
    {W cut : LinkageBlueprint Gamma Y kappa} {u v : V}
    (h : W.IsImaginaryEdgeDeletionAt cut u v) :
    W.realPart.terminals ⊆ cut.realPart.terminals := by
  intro x hx
  constructor
  · simpa only [realPart_vertices, h.vertices_eq] using hx.1
  · rintro ⟨y, hxy⟩
    exact hx.2 ⟨y, h.ordinaryExtends_original.realPart_extends.2 hxy⟩

/-- The exact one-edge cut is a real extension of the original blueprint
to the singleton consisting of the resolved tail. -/
theorem IsImaginaryEdgeDeletionAt.realExtends_cut
    {W cut : LinkageBlueprint Gamma Y kappa} {u v : V}
    (h : W.IsImaginaryEdgeDeletionAt cut u v)
    (hu : u ∈ W.realPart.terminals) : W.RealExtends cut {u} := by
  refine ⟨h.realPart_extends_cut hu, ?_⟩
  intro x hx
  by_cases hxu : x = u
  · subst x
    right
    let p : FinitePath Gamma.graph := FinitePath.trivial Gamma.graph u
    refine ⟨p, by simp [p], ?_, by simp [p, FinitePath.edgeSet], by simp [p]⟩
    simpa [p, LinkageBlueprint.realPart, h.vertices_eq] using hu.1
  · by_cases hxterm : x ∈ W.terminalSet
    · left
      left
      refine ⟨?_, hxterm⟩
      have hxNoOut := (mem_familyGraph_terminals_of_mem_terminalSet hxterm).2
      have hxvertex : x ∈ cut.vertexSet := by
        rw [h.vertices_eq]
        exact hx
      by_contra hxcutterm
      obtain ⟨y, hxycut⟩ :=
        cut.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
          hxvertex hxcutterm
      exact hxNoOut ⟨y, h.ordinaryExtends_original.2 hxycut⟩
    · left
      right
      obtain ⟨y, hxyW⟩ :=
        W.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet hx hxterm
      refine ⟨y, hxyW, ?_⟩
      change (x, y) ∈ cut.edgeSet
      rw [h.edges_eq]
      refine ⟨hxyW, ?_⟩
      intro hxy
      have hxyEq : (x, y) = (u, v) := Set.mem_singleton_iff.mp hxy
      exact hxu (Prod.mk.inj hxyEq).1

/-- In the imaginary-successor case, the exact edge-deletion cut itself is
the continuation blueprint.  Its scheduled endpoint is now a full terminal,
as required by the input of Assertion 9.31. -/
theorem IsImaginaryEdgeDeletionAt.continuation930_of_mem_slice
    {W cut : LinkageBlueprint Gamma Y kappa} {u v : V} {T B : Set V}
    (h : W.IsImaginaryEdgeDeletionAt cut u v)
    (hureal : u ∈ W.realPart.terminals) (huT : u ∈ T) :
    Continuation930 W cut cut u u T B := by
  let p : FinitePath Gamma.graph := FinitePath.trivial Gamma.graph u
  have huvertex : u ∈ cut.realPart.vertices := by
    simpa [LinkageBlueprint.realPart, h.vertices_eq] using hureal.1
  have hlinks : cut.RealLinksTo u {u} := by
    refine ⟨p, rfl, Set.mem_singleton u, ?_, ?_⟩
    · simpa [p] using huvertex
    · simp [p, FinitePath.edgeSet]
  have hlinksT : cut.RealLinksTo u T := by
    refine ⟨p, rfl, huT, ?_, ?_⟩
    · simpa [p] using huvertex
    · simp [p, FinitePath.edgeSet]
  have hpreserves :
      W.realPart.terminals \ {u} ⊆ cut.realPart.terminals :=
    fun _ hx => h.preserves_realTerminals hx.1
  exact {
    conclusion := ⟨h.isCutAt, ordinaryExtends_refl cut, hlinksT, hpreserves⟩
    links_to_endpoint := hlinks
    endpoint_mem_slice := huT
    endpoint_terminal := h.tail_mem_terminalSet
    preserves_other_terminals := hpreserves
    endpoint_fresh := by simp
    real_extends_to_endpoint := h.realExtends_cut hureal }

/-- Any legitimate cut at a real terminal already in the current slice
gives a 9.30 continuation whose endpoint is that terminal itself. -/
theorem continuation930_of_terminal_cut_mem_slice
    {W cut : LinkageBlueprint Gamma Y kappa} {u : V} {T B : Set V}
    (hcut : W.IsCutAt cut u)
    (hureal : u ∈ W.realPart.terminals) (huterm : u ∈ W.terminalSet)
    (huT : u ∈ T) :
    Continuation930 W cut W u u T B := by
  let p : FinitePath Gamma.graph := FinitePath.trivial Gamma.graph u
  have hlinks : W.RealLinksTo u {u} := by
    refine ⟨p, rfl, Set.mem_singleton u, ?_, ?_⟩
    · simpa [p, LinkageBlueprint.realPart] using hureal.1
    · simp [p, FinitePath.edgeSet]
  have hlinksT : W.RealLinksTo u T := by
    refine ⟨p, rfl, huT, ?_, ?_⟩
    · simpa [p, LinkageBlueprint.realPart] using hureal.1
    · simp [p, FinitePath.edgeSet]
  refine
    { conclusion := ?_
      links_to_endpoint := hlinks
      endpoint_mem_slice := huT
      endpoint_terminal := huterm
      preserves_other_terminals := fun _ hx => hx.1
      endpoint_fresh := by simp
      real_extends_to_endpoint := realExtends_refl W {u} }
  exact ⟨hcut, hcut.ordinaryExtends_original, hlinksT, fun _ hx => hx.1⟩

/-- Every real terminal in the scheduled slice has a concrete 9.30
continuation whose real edges are all old real edges.  The extra inclusion
is the representation-independent input needed by the scheduler's
no-new-real-predecessors invariant. -/
theorem exists_continuation930_of_real_terminal_mem_slice_with_realEdges_subset
    (W : LinkageBlueprint Gamma Y kappa) (u : V) {T B : Set V}
    (hureal : u ∈ W.realPart.terminals) (huT : u ∈ T) :
    ∃ cut : LinkageBlueprint Gamma Y kappa,
      Continuation930 W cut cut u u T B ∧
        cut.realPart.edges ⊆ W.realPart.edges := by
  rcases real_terminal_cases hureal with
      huterm | ⟨v, huv, himaginary⟩
  · exact ⟨W, continuation930_of_terminal_cut_mem_slice
      (W.isCutAt_self_of_mem_terminalSet huterm) hureal huterm huT,
        Set.Subset.rfl⟩
  · obtain ⟨cut, hcut⟩ :=
      Erdos599.Blueprint.exists_imaginaryEdgeDeletionAt W huv himaginary
    exact ⟨cut, hcut.continuation930_of_mem_slice hureal huT,
      hcut.ordinaryExtends_original.realPart_extends.2⟩

/-- Every real terminal in the scheduled slice has a concrete 9.30
continuation.  The nonterminal case uses the exact one-imaginary-edge cut,
not deletion of a whole blueprint component. -/
theorem exists_continuation930_of_real_terminal_mem_slice
    (W : LinkageBlueprint Gamma Y kappa) (u : V) {T B : Set V}
    (hureal : u ∈ W.realPart.terminals) (huT : u ∈ T) :
    ∃ cut : LinkageBlueprint Gamma Y kappa,
      Continuation930 W cut cut u u T B := by
  obtain ⟨cut, hcontinuation, _⟩ :=
    exists_continuation930_of_real_terminal_mem_slice_with_realEdges_subset
      W u hureal huT
  exact ⟨cut, hcontinuation⟩

/-- The scheduled-slice 9.30 compiler is unconditional: all required
geometry is already contained in the request premise `u ∈ T`. -/
theorem continuation930Compiler_of_scheduled_slice
    {T Z persistent B : Set V} :
    Continuation930Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B := by
  intro W u _hW _hpersistent hureal huT
  obtain ⟨cut, hcontinuation⟩ :=
    exists_continuation930_of_real_terminal_mem_slice W u hureal huT
  exact ⟨cut, cut, u, hcontinuation⟩

end LinkageBlueprint
end Blueprint
end Erdos599
