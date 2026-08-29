/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PathFilterComponents
import ErdosProblems.Erdos599.QuotientMaximal
import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Full quotient waves

The terminal-suffix quotient forgets rays and finite prefix components.
Section 6 instead needs the literal component decomposition of all surviving
vertices and edges.  This file proves that the decomposition supplied by
`PathFilterComponents.exists_quotientWarp` is already a wave.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath
open Alternating

universe u

namespace DWeb

variable {V : Type u}

/-- Components whose initial point belongs to the quotient source.  For a
full quotient of a wave, the main theorem proves that this filter removes
nothing. -/
def sourceRootedQuotientComponents (G : DWeb V) (X : Set V)
    (Q : Set (G.quotient X).DPath) : Set (G.quotient X).DPath :=
  {q | q ∈ Q ∧ q.initial ∈ (G.quotient X).source}

private theorem Ray.not_hasIncoming_initial {D : Digraph V} (r : Ray D) :
    ¬ HasIncoming r.edgeSet r.initial := by
  rintro ⟨y, n, h⟩
  have hzero : n + 1 = 0 := by
    apply r.injective
    exact (congrArg Prod.snd h).symm
  omega

private theorem Ray.hasIncoming_of_mem_support_of_ne_initial
    {D : Digraph V} (r : Ray D) {x : V} (hx : x ∈ r.support)
    (hne : x ≠ r.initial) : HasIncoming r.edgeSet x := by
  rcases hx with ⟨n, rfl⟩
  cases n with
  | zero => exact False.elim (hne rfl)
  | succ n => exact ⟨r n, n, by simp only [Nat.succ_eq_add_one]⟩

private theorem Ray.hasOutgoing_of_mem_support
    {D : Digraph V} (r : Ray D) {x : V} (hx : x ∈ r.support) :
    HasOutgoing r.edgeSet x := by
  rcases hx with ⟨n, rfl⟩
  exact ⟨r (n + 1), n, rfl⟩

/-- Strict-roof membership propagates backwards across an edge whose head
is outside the commitment set. -/
private theorem not_mem_strictRoof_of_adj_of_not_mem_strictRoof
    (G : DWeb V) {X : Set V} {y x : V}
    (hyx : G.graph.Adj y x) (hxX : x ∉ X)
    (hx : x ∉ G.strictRoof X) :
    y ∉ G.strictRoof X := by
  intro hy
  rw [G.mem_strictRoof_iff_mem_roof_sdiff_singleton] at hy
  have hxRoof : x ∉ G.roof X := by
    intro hxRoof
    exact hx ⟨hxRoof, fun hxEss ↦ hxX hxEss.1⟩
  obtain ⟨p, hp, hpAvoid⟩ := (G.not_mem_roof_iff X x).1 hxRoof
  let tail : Walk G.graph x p.finish :=
    RelationalRoof.castStart G.graph.Adj hp.1 p.walk
  let joined : Walk G.graph y p.finish := .cons hyx tail
  obtain ⟨q, hqsub⟩ :=
    RelationalRoof.exists_pathTo_support_subset (R := G.graph.Adj) joined
  let r : FinitePath G.graph :=
    { start := y
      finish := p.finish
      walk := q.1
      isPath := q.2 }
  obtain ⟨z, hzr, hzX⟩ := hy r ⟨rfl, hp.2⟩
  have hzjoined : z ∈ joined.support := hqsub hzr
  simp only [joined, Walk.support_cons, List.mem_cons] at hzjoined
  rcases hzjoined with rfl | hztail
  · exact hzX.2 rfl
  · have hzp : z ∈ p.support := by
      change z ∈ p.walk.support
      simpa only [tail, RelationalRoof.support_castStart] using hztail
    exact Set.disjoint_left.1 hpAvoid hzp hzX.1

private theorem not_hasIncoming_familyEdges_of_mem_initialSet
    (G : DWeb V) {W : Set G.DPath} (hW : G.IsWarp W)
    {x : V} (hx : x ∈ G.initialSet W) :
    ¬ HasIncoming (familyEdges W) x := by
  rintro ⟨y, hy⟩
  obtain ⟨p, hp, rfl⟩ := hx
  simp only [familyEdges, Set.mem_iUnion] at hy
  obtain ⟨q, hq, hyq⟩ := hy
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hW hp hq p.initial_mem_support
      (q.edgeSet_subset_support_prod hyq).2
  subst q
  rcases p with p | r
  · exact FinitePath.no_incoming_edge_at_start p y hyq
  · exact Ray.not_hasIncoming_initial r ⟨y, hyq⟩

private theorem hasIncoming_familyEdges_of_mem_support_of_ne_initial
    (G : DWeb V) {W : Set G.DPath} {p : G.DPath}
    (hp : p ∈ W) {x : V} (hxp : x ∈ p.support)
    (hne : x ≠ p.initial) :
    HasIncoming (familyEdges W) x := by
  rcases p with p | r
  · obtain ⟨y, hy⟩ :=
      FinitePath.exists_incoming_edge_of_mem_support_of_ne_start p hxp hne
    exact ⟨y, Set.mem_iUnion.2 ⟨(Sum.inl p : G.DPath),
      Set.mem_iUnion.2 ⟨hp, hy⟩⟩⟩
  · obtain ⟨y, hy⟩ := Ray.hasIncoming_of_mem_support_of_ne_initial r hxp hne
    exact ⟨y, Set.mem_iUnion.2 ⟨(Sum.inr r : G.DPath),
      Set.mem_iUnion.2 ⟨hp, hy⟩⟩⟩

private theorem not_hasOutgoing_familyEdges_of_mem_terminalFrontier
    (G : DWeb V) {W : Set G.DPath} (hW : G.IsWarp W)
    {x : V} (hx : x ∈ G.terminalFrontier W) :
    ¬ HasOutgoing (familyEdges W) x := by
  rintro ⟨y, hy⟩
  obtain ⟨p, hp, hpx⟩ := hx
  simp only [familyEdges, Set.mem_iUnion] at hy
  obtain ⟨q, hq, hyq⟩ := hy
  have hxp : x ∈ p.support := G.terminal_mem_support hpx
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hW hp hq hxp
      (q.edgeSet_subset_support_prod hyq).1
  subst q
  rcases p with p | r
  · simp only [DWeb.terminal?_finite, Option.some.injEq] at hpx
    subst x
    exact FinitePath.no_outgoing_edge_at_finish p y hyq
  · simp at hpx

private theorem mem_terminalFrontier_of_mem_vertexSet_of_not_hasOutgoing
    (G : DWeb V) {W : Set G.DPath} {x : V}
    (hx : x ∈ G.vertexSet W)
    (hout : ¬ HasOutgoing (familyEdges W) x) :
    x ∈ G.terminalFrontier W := by
  obtain ⟨p, hp, hxp⟩ := hx
  rcases p with p | r
  · by_cases hfinish : x = p.finish
    · exact ⟨Sum.inl p, hp, by simpa [hfinish]⟩
    · obtain ⟨y, hy⟩ :=
        FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          p hxp hfinish
      exact False.elim (hout ⟨y, Set.mem_iUnion.2
        ⟨(Sum.inl p : G.DPath), Set.mem_iUnion.2 ⟨hp, hy⟩⟩⟩)
  · obtain ⟨y, hy⟩ := Ray.hasOutgoing_of_mem_support r hxp
    exact False.elim (hout ⟨y, Set.mem_iUnion.2
      ⟨(Sum.inr r : G.DPath), Set.mem_iUnion.2 ⟨hp, hy⟩⟩⟩)

/-- Every component of the full quotient of a wave starts in the quotient
source. -/
theorem initialSet_fullQuotientComponents_subset_source
    (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source)
    {X : Set V} {U : Set G.DPath} (hU : G.IsWave U)
    {Q : Set (G.quotient X).DPath}
    (hQ : (G.quotient X).IsWarp Q)
    (hvertices : (G.quotient X).vertexSet Q =
      (G.vertexSet U ∪ X) \ G.strictRoof X)
    (hedges : familyEdges Q =
      PathFilterComponents.quotientWarpEdges G X U) :
    (G.quotient X).initialSet Q ⊆ (G.quotient X).source := by
  intro x hx
  obtain ⟨q, hqQ, hqx⟩ := hx
  have hxVertex : x ∈ (G.quotient X).vertexSet Q :=
    ⟨q, hqQ, hqx ▸ q.initial_mem_support⟩
  rw [hvertices] at hxVertex
  rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
    hNoEnter]
  refine ⟨?_, hxVertex.2⟩
  rcases hxVertex.1 with hxU | hxX
  · by_cases hxCommit : x ∈ X
    · exact Or.inr hxCommit
    · left
      obtain ⟨p, hpU, hxp⟩ := hxU
      have hxInitial : x = p.initial := by
        by_contra hne
        obtain ⟨y, hy⟩ :=
          hasIncoming_familyEdges_of_mem_support_of_ne_initial G hpU hxp hne
        apply not_hasIncoming_familyEdges_of_mem_initialSet
          (G.quotient X) hQ ⟨q, hqQ, hqx⟩
        refine ⟨y, ?_⟩
        rw [hedges]
        exact ⟨hy, familyEdges_subset_adj U hy,
          not_mem_strictRoof_of_adj_of_not_mem_strictRoof
            G (familyEdges_subset_adj U hy) hxCommit hxVertex.2,
          hxVertex.2, hxCommit⟩
      exact hxInitial ▸ hU.2.1 ⟨p, hpU, rfl⟩
  · exact Or.inr hxX

/-- The terminal classes required by Lemma 3.5 occur literally in the full
component decomposition. -/
theorem terminalFrontiers_subset_fullQuotientComponents
    (G : DWeb V) {X : Set V} {U : Set G.DPath}
    (hU : G.IsWave U) {Q : Set (G.quotient X).DPath}
    (hvertices : (G.quotient X).vertexSet Q =
      (G.vertexSet U ∪ X) \ G.strictRoof X)
    (hedges : familyEdges Q =
      PathFilterComponents.quotientWarpEdges G X U) :
    (G.terminalFrontier U \ G.strictRoof X) ∪
        (G.essential X \ G.vertexSet U) ⊆
      (G.quotient X).terminalFrontier Q := by
  rintro x (hx | hx)
  · have hxVertex : x ∈ (G.quotient X).vertexSet Q := by
      rw [hvertices]
      exact ⟨Or.inl ⟨hx.1.choose, hx.1.choose_spec.1,
        G.terminal_mem_support hx.1.choose_spec.2⟩, hx.2⟩
    apply mem_terminalFrontier_of_mem_vertexSet_of_not_hasOutgoing
      (G.quotient X) hxVertex
    intro hout
    obtain ⟨y, hy⟩ := hout
    rw [hedges] at hy
    exact not_hasOutgoing_familyEdges_of_mem_terminalFrontier G hU.1 hx.1
      ⟨y, hy.1⟩
  · have hxVertex : x ∈ (G.quotient X).vertexSet Q := by
      rw [hvertices]
      exact ⟨Or.inr hx.1.1, fun hs ↦ hs.2 hx.1⟩
    apply mem_terminalFrontier_of_mem_vertexSet_of_not_hasOutgoing
      (G.quotient X) hxVertex
    intro hout
    obtain ⟨y, hy⟩ := hout
    rw [hedges] at hy
    exact hx.2 (familyEdges_subset_vertexSet_prod U hy.1).1

/-- The literal full quotient component family is a quotient wave. -/
theorem isWave_fullQuotientComponents
    (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source)
    {X : Set V} {U : Set G.DPath} (hU : G.IsWave U)
    {Q : Set (G.quotient X).DPath}
    (hQ : (G.quotient X).IsWarp Q)
    (hvertices : (G.quotient X).vertexSet Q =
      (G.vertexSet U ∪ X) \ G.strictRoof X)
    (hedges : familyEdges Q =
      PathFilterComponents.quotientWarpEdges G X U) :
    (G.quotient X).IsWave Q := by
  apply G.isWave_of_quotientWarp_frontiers hU
  · exact hQ
  · exact G.initialSet_fullQuotientComponents_subset_source
      hNoEnter hU hQ hvertices hedges
  · exact G.terminalFrontiers_subset_fullQuotientComponents
      hU hvertices hedges

theorem sourceRootedQuotientComponents_eq
    (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source)
    {X : Set V} {U : Set G.DPath} (hU : G.IsWave U)
    {Q : Set (G.quotient X).DPath}
    (hQ : (G.quotient X).IsWarp Q)
    (hvertices : (G.quotient X).vertexSet Q =
      (G.vertexSet U ∪ X) \ G.strictRoof X)
    (hedges : familyEdges Q =
      PathFilterComponents.quotientWarpEdges G X U) :
    G.sourceRootedQuotientComponents X Q = Q := by
  ext q
  constructor
  · exact fun hq ↦ hq.1
  · intro hq
    refine ⟨hq, ?_⟩
    exact G.initialSet_fullQuotientComponents_subset_source
      hNoEnter hU hQ hvertices hedges ⟨q, hq, rfl⟩

/-- Choose the full component decomposition with exact vertex, edge, and
terminal provenance. -/
theorem exists_sourceRootedFullQuotientWave
    (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source)
    {X : Set V} {U : Set G.DPath} (hU : G.IsWave U) :
    ∃ Q : Set (G.quotient X).DPath,
      (G.quotient X).IsWave Q ∧
      G.sourceRootedQuotientComponents X Q = Q ∧
      (G.quotient X).vertexSet Q =
        (G.vertexSet U ∪ X) \ G.strictRoof X ∧
      familyEdges Q = PathFilterComponents.quotientWarpEdges G X U ∧
      (G.terminalFrontier U \ G.strictRoof X) ∪
          (G.essential X \ G.vertexSet U) ⊆
        (G.quotient X).terminalFrontier Q := by
  obtain ⟨Q, hQ, hvertices, hedges⟩ :=
    PathFilterComponents.exists_quotientWarp G X U hU.1
  refine ⟨Q,
    G.isWave_fullQuotientComponents hNoEnter hU hQ hvertices hedges,
    G.sourceRootedQuotientComponents_eq
      hNoEnter hU hQ hvertices hedges,
    hvertices, hedges, ?_⟩
  exact G.terminalFrontiers_subset_fullQuotientComponents
    hU hvertices hedges

/-- Every surviving old terminal belongs to a retained source-rooted full
component and is its finite terminal. -/
theorem exists_sourceRootedFullQuotientComponent_of_mem_terminalFrontier
    (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source)
    {X : Set V} {U : Set G.DPath} (hU : G.IsWave U)
    {Q : Set (G.quotient X).DPath}
    (hQ : (G.quotient X).IsWarp Q)
    (hvertices : (G.quotient X).vertexSet Q =
      (G.vertexSet U ∪ X) \ G.strictRoof X)
    (hedges : familyEdges Q =
      PathFilterComponents.quotientWarpEdges G X U)
    {x : V} (hx : x ∈ G.terminalFrontier U \ G.strictRoof X) :
    ∃ q ∈ G.sourceRootedQuotientComponents X Q,
      (G.quotient X).terminal? q = some x ∧ x ∈ q.support := by
  have hxTerminal : x ∈ (G.quotient X).terminalFrontier Q :=
    G.terminalFrontiers_subset_fullQuotientComponents
      hU hvertices hedges (Or.inl hx)
  obtain ⟨q, hqQ, hqx⟩ := hxTerminal
  refine ⟨q, ?_, hqx, (G.quotient X).terminal_mem_support hqx⟩
  exact ⟨hqQ,
    G.initialSet_fullQuotientComponents_subset_source
      hNoEnter hU hQ hvertices hedges ⟨q, hqQ, rfl⟩⟩

end DWeb

#print axioms DWeb.exists_sourceRootedFullQuotientWave

end Erdos599
