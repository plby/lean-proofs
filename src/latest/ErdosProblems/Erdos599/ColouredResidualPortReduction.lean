/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredResidualPortContinuation
import ErdosProblems.Erdos599.SafeSwitchingRelationalBalance
import ErdosProblems.Erdos599.SafeSwitchingRelationalReduction

/-!
# Finite reducing switches from coloured residual port paths

A simple finite path in the coloured residual port relation records both
actual edges and the identity edges which complete the reference matching.
The identity steps have zero ambient boundary.  This file erases precisely
those diagonal steps, extracts the finite inserted and removed relations,
and proves the reducing balance directly from the endpoint balance of the
port path.

No interval-convexity or alternating-path realization is used.
-/

namespace Erdos599
namespace ColouredResidualPortReduction

open Set DirectedPath Alternating
open TwoWarpMatchingTraversal
open ColouredResidualPortContinuation
open Alternating.SwitchingCore.RelationalInterval
open Alternating.SwitchingCore.RelationalReduction

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The coloured residual relation, regarded as a directed graph. -/
def residualPortDigraph (Z Y : Set Gamma.DPath) : Digraph (Port V) where
  Adj := ResidualStep Z Y

/-- Embed an ambient edge as a sending-to-receiving port edge. -/
def forwardPortEdge (e : V × V) : Port V × Port V :=
  (.inl e.1, .inr e.2)

/-- Embed an ambient edge in the reverse-reference traversal direction. -/
def backwardPortEdge (e : V × V) : Port V × Port V :=
  (.inr e.2, .inl e.1)

theorem forwardPortEdge_injective :
    Function.Injective (forwardPortEdge : V × V → Port V × Port V) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [forwardPortEdge, Prod.mk.injEq, Sum.inl.injEq,
    Sum.inr.injEq] at h
  exact Prod.ext h.1 h.2

theorem backwardPortEdge_injective :
    Function.Injective (backwardPortEdge : V × V → Port V × Port V) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [backwardPortEdge, Prod.mk.injEq, Sum.inr.injEq,
    Sum.inl.injEq] at h
  exact Prod.ext h.2 h.1

/-- All sending-to-receiving occurrences of the port path, including
identity occurrences. -/
def fullForwardEdges {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) : Set (V × V) :=
  forwardPortEdge ⁻¹' P.edgeSet

/-- All receiving-to-sending occurrences, including completed-matching
identity occurrences. -/
def fullBackwardEdges {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) : Set (V × V) :=
  backwardPortEdge ⁻¹' P.edgeSet

/-- Actual inserted forward edges: diagonal completion steps are omitted. -/
def forwardEdges {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) : Set (V × V) :=
  {e | e ∈ fullForwardEdges P ∧ e.1 ≠ e.2}

/-- Actual removed reference edges: diagonal completion steps are omitted. -/
def backwardEdges {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) : Set (V × V) :=
  {e | e ∈ fullBackwardEdges P ∧ e.1 ≠ e.2}

theorem fullForwardEdges_finite {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) :
    (fullForwardEdges P).Finite := by
  exact (Alternating.Walk.edgeSet_finite P.walk).preimage
    forwardPortEdge_injective.injOn

theorem fullBackwardEdges_finite {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) :
    (fullBackwardEdges P).Finite := by
  exact (Alternating.Walk.edgeSet_finite P.walk).preimage
    backwardPortEdge_injective.injOn

theorem forwardEdges_finite {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) :
    (forwardEdges P).Finite :=
  (fullForwardEdges_finite P).subset (fun _ he ↦ he.1)

theorem backwardEdges_finite {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) :
    (backwardEdges P).Finite :=
  (fullBackwardEdges_finite P).subset (fun _ he ↦ he.1)

private theorem fullForwardEdges_biUnique {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ fullForwardEdges P) := by
  have hP := Alternating.FinitePath.edgeSet_biUnique P
  constructor
  · intro a b x hax hbx
    have h := hP.1 hax hbx
    exact Sum.inl.inj h
  · intro x a b hxa hxb
    have h := hP.2 hxa hxb
    exact Sum.inr.inj h

private theorem fullBackwardEdges_biUnique {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ fullBackwardEdges P) := by
  have hP := Alternating.FinitePath.edgeSet_biUnique P
  constructor
  · intro a b x hax hbx
    have h := hP.2 hax hbx
    exact Sum.inl.inj h
  · intro x a b hxa hxb
    have h := hP.1 hxa hxb
    exact Sum.inr.inj h

private theorem edgeBalance_nonDiagonal_eq
    {E : Set (V × V)}
    (hE : Relator.BiUnique (fun x y ↦ (x, y) ∈ E)) (x : V) :
    edgeBalance {e | e ∈ E ∧ e.1 ≠ e.2} x = edgeBalance E x := by
  classical
  by_cases hloop : (x, x) ∈ E
  · have houtOld : HasOutgoing E x := ⟨x, hloop⟩
    have hinOld : HasIncoming E x := ⟨x, hloop⟩
    have houtNew : ¬HasOutgoing {e | e ∈ E ∧ e.1 ≠ e.2} x := by
      rintro ⟨y, hy⟩
      rcases hy with ⟨hyE, hxy⟩
      change (x, y) ∈ E at hyE
      have heq : y = x := by
        exact hE.2 hyE hloop
      exact hxy (by simpa only using heq.symm)
    have hinNew : ¬HasIncoming {e | e ∈ E ∧ e.1 ≠ e.2} x := by
      rintro ⟨y, hy⟩
      rcases hy with ⟨hyE, hyx⟩
      change (y, x) ∈ E at hyE
      have heq : y = x := by
        exact hE.1 hyE hloop
      exact hyx (by simpa only using heq)
    simp [edgeBalance, propInt, houtOld, hinOld, houtNew, hinNew]
  · have hout : HasOutgoing {e | e ∈ E ∧ e.1 ≠ e.2} x ↔
        HasOutgoing E x := by
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y, hy.1⟩
      · rintro ⟨y, hy⟩
        refine ⟨y, hy, ?_⟩
        intro hxy
        change x = y at hxy
        exact hloop (by simpa [hxy] using hy)
    have hin : HasIncoming {e | e ∈ E ∧ e.1 ≠ e.2} x ↔
        HasIncoming E x := by
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y, hy.1⟩
      · rintro ⟨y, hy⟩
        refine ⟨y, hy, ?_⟩
        intro hyx
        change y = x at hyx
        exact hloop (by simpa [hyx] using hy)
    simp only [edgeBalance, hout, hin]

private theorem path_outgoing_inl_iff {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) (x : V) :
    HasOutgoing P.edgeSet (.inl x) ↔ HasOutgoing (fullForwardEdges P) x := by
  constructor
  · rintro ⟨q, hq⟩
    have hadj := P.edgeSet_subset_adj hq
    rcases q with y | y
    · exact False.elim hadj
    · exact ⟨y, hq⟩
  · rintro ⟨y, hy⟩
    exact ⟨.inr y, hy⟩

private theorem path_incoming_inl_iff {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) (x : V) :
    HasIncoming P.edgeSet (.inl x) ↔ HasOutgoing (fullBackwardEdges P) x := by
  constructor
  · rintro ⟨q, hq⟩
    have hadj := P.edgeSet_subset_adj hq
    rcases q with y | y
    · exact False.elim hadj
    · exact ⟨y, hq⟩
  · rintro ⟨y, hy⟩
    exact ⟨.inr y, hy⟩

private theorem path_outgoing_inr_iff {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) (x : V) :
    HasOutgoing P.edgeSet (.inr x) ↔ HasIncoming (fullBackwardEdges P) x := by
  constructor
  · rintro ⟨q, hq⟩
    have hadj := P.edgeSet_subset_adj hq
    rcases q with y | y
    · exact ⟨y, hq⟩
    · exact False.elim hadj
  · rintro ⟨y, hy⟩
    exact ⟨.inl y, hy⟩

private theorem path_incoming_inr_iff {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) (x : V) :
    HasIncoming P.edgeSet (.inr x) ↔ HasIncoming (fullForwardEdges P) x := by
  constructor
  · rintro ⟨q, hq⟩
    have hadj := P.edgeSet_subset_adj hq
    rcases q with y | y
    · exact ⟨y, hq⟩
    · exact False.elim hadj
  · rintro ⟨y, hy⟩
    exact ⟨.inl y, hy⟩

private theorem fullEdgeBalance_eq_portBalance {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) (x : V) :
    edgeBalance (fullForwardEdges P) x -
        edgeBalance (fullBackwardEdges P) x =
      edgeBalance P.edgeSet (.inl x) + edgeBalance P.edgeSet (.inr x) := by
  simp only [edgeBalance, path_outgoing_inl_iff P x,
    path_incoming_inl_iff P x, path_outgoing_inr_iff P x,
    path_incoming_inr_iff P x]
  omega

/-- The non-diagonal extracted relations have exactly the reducing boundary
of a residual path from the receiving port of `v` to the sending port of
`u`. -/
theorem edgeBalance_forward_sub_backward {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) {u v : V}
    (hstart : P.start = .inr v) (hfinish : P.finish = .inl u) (x : V) :
    edgeBalance (forwardEdges P) x - edgeBalance (backwardEdges P) x =
      propInt (x = v) - propInt (x = u) := by
  have hne : P.start ≠ P.finish := by
    rw [hstart, hfinish]
    exact Sum.inr_ne_inl
  unfold forwardEdges backwardEdges
  rw [edgeBalance_nonDiagonal_eq (fullForwardEdges_biUnique P),
    edgeBalance_nonDiagonal_eq (fullBackwardEdges_biUnique P),
    fullEdgeBalance_eq_portBalance]
  rw [Alternating.FinitePath.edgeBalance_eq_endpoints P hne,
    Alternating.FinitePath.edgeBalance_eq_endpoints P hne, hstart, hfinish]
  have hinl : propInt ((.inl x : Port V) = .inl u) = propInt (x = u) := by
    apply congrArg propInt
    apply propext
    exact ⟨Sum.inl.inj, congrArg Sum.inl⟩
  have hinr : propInt ((.inr x : Port V) = .inr v) = propInt (x = v) := by
    apply congrArg propInt
    apply propext
    exact ⟨Sum.inr.inj, congrArg Sum.inr⟩
  rw [hinl, hinr]
  simp only [Sum.inl_ne_inr, Sum.inr_ne_inl, propInt]
  omega

theorem forwardEdges_subset_familyEdges {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) :
    forwardEdges P ⊆ familyEdges Y := by
  rintro ⟨x, y⟩ ⟨hP, hxy⟩
  have hadj := P.edgeSet_subset_adj hP
  exact hadj.1.resolve_right hxy

theorem forwardEdges_disjoint_familyEdges {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) :
    Disjoint (forwardEdges P) (familyEdges Z) := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ ⟨hP, _hxy⟩ hZ
  exact (P.edgeSet_subset_adj hP).2 (matchingEdge_actual hZ)

theorem backwardEdges_subset_familyEdges {Z Y : Set Gamma.DPath}
    (P : FinitePath (residualPortDigraph Z Y)) :
    backwardEdges P ⊆ familyEdges Z := by
  rintro ⟨x, y⟩ ⟨hP, hxy⟩
  have hadj := P.edgeSet_subset_adj hP
  rcases hadj with hactual | hidentity
  · exact hactual
  · exact False.elim (hxy hidentity.1)

private theorem matching_biUnique {Z : Set Gamma.DPath}
    (hZ : Gamma.IsWarp Z) :
    Relator.BiUnique (completedReferenceMatching Z) :=
  matchingEdge_biUnique hZ

/-- Every old reference incidence conflicting at the head of an inserted
edge occurs as an actual reverse step of the residual path. -/
theorem incoming_reference_removed {Z Y : Set Gamma.DPath}
    (hZ : Gamma.IsWarp Z) (P : FinitePath (residualPortDigraph Z Y))
    {u : V} (hfinishP : P.finish = .inl u)
    {a b x : V} (hax : (a, x) ∈ forwardEdges P)
    (hbx : (b, x) ∈ familyEdges Z) :
    (b, x) ∈ backwardEdges P := by
  rcases hax with ⟨haxP, haxne⟩
  have hxSupport : (.inr x : Port V) ∈ P.support :=
    (P.edgeSet_subset_support_prod haxP).2
  have hxFinish : (.inr x : Port V) ≠ P.finish := by
    rw [hfinishP]
    exact Sum.inr_ne_inl
  obtain ⟨q, hq⟩ :=
    Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      P hxSupport hxFinish
  have hadj := P.edgeSet_subset_adj hq
  rcases q with c | c
  · have hbc : b = c := (matching_biUnique hZ).1
        (matchingEdge_actual hbx) hadj
    subst c
    refine ⟨hq, ?_⟩
    intro h
    change b = x at h
    exact not_self_mem_familyEdges Z x (by simpa [h] using hbx)
  · exact False.elim hadj

/-- Every old reference incidence conflicting at the tail of an inserted
edge occurs as an actual reverse step of the residual path. -/
theorem outgoing_reference_removed {Z Y : Set Gamma.DPath}
    (hZ : Gamma.IsWarp Z) (P : FinitePath (residualPortDigraph Z Y))
    {v : V} (hstartP : P.start = .inr v)
    {x a b : V} (hxa : (x, a) ∈ forwardEdges P)
    (hxb : (x, b) ∈ familyEdges Z) :
    (x, b) ∈ backwardEdges P := by
  rcases hxa with ⟨hxaP, hxane⟩
  have hxSupport : (.inl x : Port V) ∈ P.support :=
    (P.edgeSet_subset_support_prod hxaP).1
  have hxStart : (.inl x : Port V) ≠ P.start := by
    rw [hstartP]
    exact Sum.inl_ne_inr
  obtain ⟨q, hq⟩ :=
    Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
      P hxSupport hxStart
  have hadj := P.edgeSet_subset_adj hq
  rcases q with c | c
  · exact False.elim hadj
  · have hbc : b = c := (matching_biUnique hZ).2
        (matchingEdge_actual hxb) hadj
    subst c
    refine ⟨hq, ?_⟩
    intro h
    change x = b at h
    exact not_self_mem_familyEdges Z x (by simpa [h] using hxb)

/-- A finite simple residual port path produces an honest finite-character
reducing warp.  Actual inserted edges come from `Y`, actual reverse edges
are removed from `Z`, while matching-completion diagonals are ignored. -/
theorem exists_reducingWarp_of_residualPortPath
    {Z Y : Set Gamma.DPath}
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z)
    (_hYfinite : Gamma.HasFiniteCharacter Y)
    (P : FinitePath (residualPortDigraph Z Y)) {u v : V}
    (hstart : P.start = .inr v) (hfinish : P.finish = .inl u)
    (hu : u ∈ Gamma.initialSet Z) (huNonisolated : u ∉ isolatedVertices Z)
    (hv : v ∈ Gamma.terminalFrontier Z)
    (hvNonisolated : v ∉ isolatedVertices Z)
    (hYpure : ∀ {x y : V}, (x, y) ∈ familyEdges Y →
      y ∉ Gamma.initialSet Z ∧ x ∉ Gamma.terminalFrontier Z) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U ⊆
        (familyEdges Z \ backwardEdges P) ∪ forwardEdges P ∧
      isolatedVertices U = isolatedVertices Z ∧
      (∀ x, edgeBalance (familyEdges U) x =
        edgeBalance ((familyEdges Z \ backwardEdges P) ∪ forwardEdges P) x) ∧
      Gamma.initialSet U = Gamma.initialSet Z \ {u} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Z \ {v} := by
  let E := (familyEdges Z \ backwardEdges P) ∪ forwardEdges P
  have hFsub := forwardEdges_subset_familyEdges P
  have hRsub := backwardEdges_subset_familyEdges P
  have hin : ∀ {a b x : V}, (a, x) ∈ forwardEdges P →
      (b, x) ∈ familyEdges Z → (b, x) ∈ backwardEdges P :=
    by
      intro a b x hax hbx
      exact incoming_reference_removed hZ P hfinish hax hbx
  have hout : ∀ {x a b : V}, (x, a) ∈ forwardEdges P →
      (x, b) ∈ familyEdges Z → (x, b) ∈ backwardEdges P :=
    by
      intro x a b hxa hxb
      exact outgoing_reference_removed hZ P hstart hxa hxb
  have hbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    dsimp [E]
    exact biUnique_of_incident_reference_edges_removed hY hZ hFsub hin hout
  have hiso : ∀ x ∈ isolatedVertices Z, ∀ y,
      (x, y) ∉ E ∧ (y, x) ∉ E := by
    intro x hx y
    have hxInitial : x ∈ Gamma.initialSet Z :=
      ⟨Gamma.trivialPath x, hx, by simp⟩
    have hxTerminal : x ∈ Gamma.terminalFrontier Z :=
      ⟨Gamma.trivialPath x, hx, by simp⟩
    constructor
    · rintro (he | he)
      · exact not_isolated_of_hasOutgoing hZ ⟨y, he.1⟩ hx
      · exact (hYpure (hFsub he)).2 hxTerminal
    · rintro (he | he)
      · exact not_isolated_of_hasIncoming hZ ⟨y, he.1⟩ hx
      · exact (hYpure (hFsub he)).1 hxInitial
  apply exists_finiteWarp_reducing_of_finiteRelationalSwitch
    hZ hZfinite hRsub (backwardEdges_finite P) (forwardEdges_finite P)
    (hFsub.trans (familyEdges_subset_adj Y))
    (forwardEdges_disjoint_familyEdges P) rfl hbi hiso
    hu huNonisolated hv hvNonisolated
  exact fun x ↦ edgeBalance_forward_sub_backward P hstart hfinish x

#print axioms edgeBalance_forward_sub_backward
#print axioms incoming_reference_removed
#print axioms outgoing_reference_removed
#print axioms exists_reducingWarp_of_residualPortPath

end ColouredResidualPortReduction
end Erdos599
