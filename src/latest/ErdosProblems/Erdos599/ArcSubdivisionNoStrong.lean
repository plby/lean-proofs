/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Blueprint
import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Real edges of a directed-arc subdivision are not strong imaginary edges

This file isolates the local observation used by the subdivision reduction.
Every retained edge has a midpoint at one of its ends.  At that midpoint the
edge is the unique incoming or outgoing edge, and all edges on the other side
have one fixed endpoint away from the two ends of the retained edge.

The formulation is hereditary: it does not require that the companion edge
still be present.  Thus it survives all of the induced-subgraph, deletion,
quotient, and essential-part operations used by the ladder construction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint

open Alternating DirectedPath

universe u

variable {V : Type u}

/-- Local incidence pattern of one edge of a directed-arc subdivision.

In the first alternative `v` is the midpoint: `u` is its only possible
predecessor and `w` its only possible successor.  In the second alternative
`u` is the midpoint, with the dual incidence pattern.  The companion edge is
not required to exist, which makes the predicate hereditary under deleting
edges. -/
def HasSubdivisionIncidenceAt (D : Digraph V) (u v : V) : Prop :=
  u ≠ v ∧
    ((∃ w, w ≠ u ∧ w ≠ v ∧
        (∀ ⦃x⦄, D.Adj x v → x = u) ∧
        (∀ ⦃y⦄, D.Adj v y → y = w)) ∨
      (∃ w, w ≠ u ∧ w ≠ v ∧
        (∀ ⦃y⦄, D.Adj u y → y = v) ∧
        (∀ ⦃x⦄, D.Adj x u → x = w)))

/-- Every edge has the local incidence pattern of one half of a subdivided
directed arc. -/
def HasHereditarySubdivisionIncidence (D : Digraph V) : Prop :=
  ∀ ⦃u v⦄, D.Adj u v → HasSubdivisionIncidenceAt D u v

/-- The incidence pattern is inherited by an arbitrary subrelation. -/
theorem HasHereditarySubdivisionIncidence.of_adj_imp
    {D E : Digraph V} (hD : HasHereditarySubdivisionIncidence D)
    (hED : ∀ ⦃x y⦄, E.Adj x y → D.Adj x y) :
    HasHereditarySubdivisionIncidence E := by
  intro u v huv
  rcases hD (hED huv) with ⟨huvne,
    (⟨w, hwu, hwv, hin, hout⟩ | ⟨w, hwu, hwv, hout, hin⟩)⟩
  · exact ⟨huvne, Or.inl ⟨w, hwu, hwv,
      fun _ h ↦ hin (hED h), fun _ h ↦ hout (hED h)⟩⟩
  · exact ⟨huvne, Or.inr ⟨w, hwu, hwv,
      fun _ h ↦ hout (hED h), fun _ h ↦ hin (hED h)⟩⟩

private def oneEdgeFinitePath {D : Digraph V} {u v : V}
    (huv : D.Adj u v) (hne : u ≠ v) : FinitePath D where
  start := u
  finish := v
  walk := .cons huv .nil
  isPath := by
    simp only [Walk.IsPath, Walk.support_cons, Walk.support_nil]
    simp [hne]

private theorem oneEdgeFinitePath_edgeSet {D : Digraph V} {u v : V}
    (huv : D.Adj u v) (hne : u ≠ v) :
    (oneEdgeFinitePath huv hne).edgeSet = {(u, v)} := by
  simp [oneEdgeFinitePath, FinitePath.edgeSet, Walk.edgeSet]

private theorem not_familyEdge_of_right_not_mem_vertexSet
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {u v : V}
    (hv : v ∉ Gamma.vertexSet Y) :
    (u, v) ∉ familyEdges Y := by
  intro huv
  simp only [familyEdges, Set.mem_iUnion] at huv
  obtain ⟨p, hpY, hpedge⟩ := huv
  exact hv ⟨p, hpY, (p.edgeSet_subset_support_prod hpedge).2⟩

private theorem not_familyEdge_of_left_not_mem_vertexSet
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {u v : V}
    (hu : u ∉ Gamma.vertexSet Y) :
    (u, v) ∉ familyEdges Y := by
  intro huv
  simp only [familyEdges, Set.mem_iUnion] at huv
  obtain ⟨p, hpY, hpedge⟩ := huv
  exact hu ⟨p, hpY, (p.edgeSet_subset_support_prod hpedge).1⟩

private theorem isDegenerate_of_direct_switched_edge
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    {u v : V} (huv : Gamma.graph.Adj u v) (hne : u ≠ v)
    (hinitial : Q.initial = u) (hedge : (u, v) ∈ Q.edgeSet)
    (hnotY : (u, v) ∉ familyEdges Y) :
    IsDegenerate Y Q (.vertex v) := by
  let p : FinitePath Gamma.graph := oneEdgeFinitePath huv hne
  refine ⟨p, hinitial.symm, rfl, ?_, Or.inl hne⟩
  rw [Cyclowarp.application_edges]
  intro e he
  have heq : e = (u, v) := by
    simpa only [p, oneEdgeFinitePath_edgeSet, Set.mem_singleton_iff] using he
  subst e
  exact Or.inr ⟨hedge, hnotY⟩

private theorem lastLink_support_subset_vertexSet
    {D : Digraph V} (Q : FiniteTrace D) :
    Q.lastLink.path.support ⊆ (AltPath.finite Q).vertexSet := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨⟨Q.lastIndex, Nat.lt_succ_self _⟩, hx⟩

private theorem firstLink_support_subset_vertexSet
    {D : Digraph V} (Q : FiniteTrace D) :
    Q.firstLink.path.support ⊆ (AltPath.finite Q).vertexSet := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨⟨0, Nat.zero_lt_succ _⟩, hx⟩

private theorem lastLink_edgeSet_subset
    {D : Digraph V} (Q : FiniteTrace D) :
    Q.lastLink.path.edgeSet ⊆ (AltPath.finite Q).edgeSet := by
  intro e he
  exact Set.mem_iUnion.2 ⟨⟨Q.lastIndex, Nat.lt_succ_self _⟩, he⟩

private theorem firstLink_edgeSet_subset
    {D : Digraph V} (Q : FiniteTrace D) :
    Q.firstLink.path.edgeSet ⊆ (AltPath.finite Q).edgeSet := by
  intro e he
  exact Set.mem_iUnion.2 ⟨⟨0, Nat.zero_lt_succ _⟩, he⟩

private theorem common_successor_mem_hammockInterior
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {u v w : V}
    (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (hin : ∀ ⦃x⦄, Gamma.graph.Adj x v → x = u)
    (hout : ∀ ⦃y⦄, Gamma.graph.Adj v y → y = w)
    {H : Set (AltPath Gamma.graph)}
    (hH : NondegenerateHammock Gamma Y u (.vertex v) H)
    {Q : AltPath Gamma.graph} (hQH : Q ∈ H) :
    w ∈ hammockInterior u (.vertex v) Q := by
  obtain ⟨hSafe, hinitial, hend⟩ := hH.1.1 Q hQH
  have hnondeg := hH.2 Q hQH
  rcases Q with (z | T | T)
  · have hend' : z = v := by simpa [HasEnd] using hend
    exact (huv (hinitial.symm.trans hend')).elim
  · have hterminal : T.terminal = v := by simpa [HasEnd] using hend
    cases hdir : T.lastLink.direction with
    | forward =>
        have hfinish : T.lastLink.path.finish = v := by
          simpa [FiniteTrace.terminal, Link.exit, hdir] using hterminal
        obtain ⟨x, hxedge⟩ :=
          FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
            T.lastLink.path T.lastLink.path.finish_mem_support
            (Ne.symm T.lastLink.nontrivial)
        have hxadj : Gamma.graph.Adj x T.lastLink.path.finish :=
          T.lastLink.path.edgeSet_subset_adj hxedge
        have hxu : x = u := hin (hfinish ▸ hxadj)
        have hedge : (u, v) ∈ (AltPath.finite T).edgeSet := by
          apply lastLink_edgeSet_subset T
          simpa [hxu, hfinish] using hxedge
        have hvY : v ∉ Gamma.vertexSet Y := by
          exact hSafe.isAlternating.2.2.2 v hend (by
            simpa only [AltPath.lastDirection?] using congrArg some hdir)
        have huvadj : Gamma.graph.Adj u v := by
          simpa [hxu, hfinish] using hxadj
        exact (hnondeg (isDegenerate_of_direct_switched_edge
          huvadj huv
          hinitial hedge (not_familyEdge_of_right_not_mem_vertexSet hvY))).elim
    | backward =>
        have hstart : T.lastLink.path.start = v := by
          simpa [FiniteTrace.terminal, Link.exit, hdir] using hterminal
        obtain ⟨y, hyedge⟩ :=
          FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            T.lastLink.path T.lastLink.path.start_mem_support
            T.lastLink.nontrivial
        have hyadj : Gamma.graph.Adj T.lastLink.path.start y :=
          T.lastLink.path.edgeSet_subset_adj hyedge
        have hyw : y = w := hout (hstart ▸ hyadj)
        have hwSupport : w ∈ T.lastLink.path.support := by
          rw [← hyw]
          exact (T.lastLink.path.edgeSet_subset_support_prod hyedge).2
        refine ⟨lastLink_support_subset_vertexSet T
          hwSupport, ?_⟩
        simp only [hammockEndpoints, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or]
        exact ⟨by simpa [hyw] using hwu, by simpa [hyw] using hwv⟩
  · simp [HasEnd] at hend

private theorem common_predecessor_mem_hammockInterior
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {u v w : V}
    (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (hout : ∀ ⦃y⦄, Gamma.graph.Adj u y → y = v)
    (hin : ∀ ⦃x⦄, Gamma.graph.Adj x u → x = w)
    {H : Set (AltPath Gamma.graph)}
    (hH : NondegenerateHammock Gamma Y u (.vertex v) H)
    {Q : AltPath Gamma.graph} (hQH : Q ∈ H) :
    w ∈ hammockInterior u (.vertex v) Q := by
  obtain ⟨hSafe, hinitial, hend⟩ := hH.1.1 Q hQH
  have hnondeg := hH.2 Q hQH
  rcases Q with (z | T | T)
  · have hend' : z = v := by simpa [HasEnd] using hend
    exact (huv (hinitial.symm.trans hend')).elim
  · have hinitialT : T.initial = u := hinitial
    cases hdir : T.firstLink.direction with
    | forward =>
        have hstart : T.firstLink.path.start = u := by
          simpa [FiniteTrace.initial, Link.entry, hdir] using hinitialT
        obtain ⟨y, hyedge⟩ :=
          FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            T.firstLink.path T.firstLink.path.start_mem_support
            T.firstLink.nontrivial
        have hyadj : Gamma.graph.Adj T.firstLink.path.start y :=
          T.firstLink.path.edgeSet_subset_adj hyedge
        have hyv : y = v := hout (hstart ▸ hyadj)
        have hedge : (u, v) ∈ (AltPath.finite T).edgeSet := by
          apply firstLink_edgeSet_subset T
          simpa [hstart, hyv] using hyedge
        have huY : u ∉ Gamma.vertexSet Y := by
          have h := hSafe.isAlternating.2.2.1 (by
            simpa only [AltPath.firstDirection?] using congrArg some hdir)
          simpa only [hinitial] using h
        have huvadj : Gamma.graph.Adj u v := by
          simpa [hstart, hyv] using hyadj
        exact (hnondeg (isDegenerate_of_direct_switched_edge
          huvadj huv
          hinitial hedge (not_familyEdge_of_left_not_mem_vertexSet huY))).elim
    | backward =>
        have hfinish : T.firstLink.path.finish = u := by
          simpa [FiniteTrace.initial, Link.entry, hdir] using hinitialT
        obtain ⟨x, hxedge⟩ :=
          FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
            T.firstLink.path T.firstLink.path.finish_mem_support
            (Ne.symm T.firstLink.nontrivial)
        have hxadj : Gamma.graph.Adj x T.firstLink.path.finish :=
          T.firstLink.path.edgeSet_subset_adj hxedge
        have hxw : x = w := hin (hfinish ▸ hxadj)
        have hwSupport : w ∈ T.firstLink.path.support := by
          rw [← hxw]
          exact (T.firstLink.path.edgeSet_subset_support_prod hxedge).1
        refine ⟨firstLink_support_subset_vertexSet T
          hwSupport, ?_⟩
        simp only [hammockEndpoints, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or]
        exact ⟨by simpa [hxw] using hwu, by simpa [hxw] using hwv⟩
  · simp [HasEnd] at hend

/-- A nondegenerate hammock at an edge with subdivision incidence contains
at most one alternating path. -/
theorem NondegenerateHammock.subsingleton_of_subdivisionIncidence
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {u v : V}
    {H : Set (AltPath Gamma.graph)}
    (hH : NondegenerateHammock Gamma Y u (.vertex v) H)
    (hinc : HasSubdivisionIncidenceAt Gamma.graph u v) :
    H.Subsingleton := by
  intro Q hQ R hR
  by_contra hQR
  rcases hinc with ⟨huv,
    (⟨w, hwu, hwv, hin, hout⟩ | ⟨w, hwu, hwv, hout, hin⟩)⟩
  · exact Set.disjoint_left.1 (hH.1.2 hQ hR hQR)
      (common_successor_mem_hammockInterior huv hwu hwv hin hout hH hQ)
      (common_successor_mem_hammockInterior huv hwu hwv hin hout hH hR)
  · exact Set.disjoint_left.1 (hH.1.2 hQ hR hQR)
      (common_predecessor_mem_hammockInterior huv hwu hwv hout hin hH hQ)
      (common_predecessor_mem_hammockInterior huv hwu hwv hout hin hH hR)

/-- No edge with subdivision incidence is a strong imaginary edge at an
infinite cardinal. -/
theorem not_isStrongImaginaryEdge_of_subdivisionIncidence
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) {u v : V}
    (hinc : HasSubdivisionIncidenceAt Gamma.graph u v) :
    ¬ IsStrongImaginaryEdge Gamma Y kappa u v := by
  rintro ⟨H, hH, hcard⟩
  have hle : #H ≤ 1 :=
    (hH.subsingleton_of_subdivisionIncidence hinc).cardinalMk_le_one
  have hone : (1 : Cardinal.{u}) < succ kappa :=
    (Cardinal.one_le_aleph0.trans hkappa).trans_lt (lt_succ kappa)
  rw [hcard] at hle
  exact (not_le_of_gt hone) hle

/-- Uniform edge form of the preceding theorem. -/
theorem HasHereditarySubdivisionIncidence.no_strongImaginaryEdge
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
    (hGamma : HasHereditarySubdivisionIncidence Gamma.graph)
    (hkappa : aleph0 ≤ kappa) {u v : V}
    (huv : Gamma.graph.Adj u v) :
    ¬ IsStrongImaginaryEdge Gamma Y kappa u v :=
  not_isStrongImaginaryEdge_of_subdivisionIncidence hkappa (hGamma huv)

#print axioms NondegenerateHammock.subsingleton_of_subdivisionIncidence
#print axioms not_isStrongImaginaryEdge_of_subdivisionIncidence
#print axioms HasHereditarySubdivisionIncidence.no_strongImaginaryEdge

end Blueprint
end Erdos599
