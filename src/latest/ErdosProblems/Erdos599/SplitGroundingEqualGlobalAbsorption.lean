/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualOrderedTargetContact
import ErdosProblems.Erdos599.SplitGroundingEqualStrictCompiler
import ErdosProblems.Erdos599.SplitGroundingEqualTargetCoverage

/-!
# The remaining global absorption obstruction in the split equal branch

The ordered strict-route construction roots a point of each selected
route's own target component.  This does not by itself cover an untouched
hanging component of the limiting ladder.  In fact, for the fixed repaired
relation of the strict selected family, such a component cannot be rooted
from the original source when no edge enters that source.

This file records the obstruction at exactly the interface exposed by
`splitReachableTerminalCut_sourceRooted_or_routeContact_or_untouchedHanging`.
Consequently the whole-family argument must eliminate the untouched case
by a maximality/augmentation theorem which produces a selected-route
contact.  The ambient source path carried by the reachable cut is not, on
its own, part of the repaired relation.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}

private abbrev SplitGlobalInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

/-- Under source normalization, a hanging path contains no original source
vertex. -/
private theorem split_support_disjoint_source_of_hanging
    (p : Gamma.DPath)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hhang : PopularAuxiliary.IsHangingPath Gamma p) :
    Disjoint p.support Gamma.source := by
  rw [Set.disjoint_left]
  intro x hxp hxsource
  have hno : ¬ Alternating.HasIncoming
      (Alternating.familyEdges ({p} : Set Gamma.DPath)) x := by
    rintro ⟨y, hyx⟩
    exact hNoEnter
      (Alternating.familyEdges_subset_adj ({p} : Set Gamma.DPath) hyx)
      hxsource
  have hinitial : p.initial = x :=
    Alternating.initial_eq_of_mem_support_of_noIncoming
      (W := ({p} : Set Gamma.DPath)) (p := p) (by simp) hxp hno
  exact hhang (hinitial.symm ▸ hxsource)

/-- If every actual erased route avoids a limiting-ladder component, every
inserted forward edge avoids both endpoints of that component. -/
private theorem split_forwardEdges_endpoints_not_mem_of_route_disjoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    (W : Popular.XSWarp
      (SplitGlobalInput L hL).lambda (SplitGlobalInput L hL).lambda.target)
    (Y : Gamma.DPath)
    (havoid : ∀ r : WarpPath W,
      Disjoint
        (canonicalErasedRoute (SplitGlobalInput L hL) W r).vertexSet
        Y.support)
    {e : V × V}
    (he : e ∈ canonicalErasedForwardEdges (SplitGlobalInput L hL) W) :
    e.1 ∉ Y.support ∧ e.2 ∉ Y.support := by
  simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at he
  obtain ⟨r, hre⟩ := he
  have hends := AltPath.directionEdge_endpoints_mem_vertexSet
    (canonicalErasedRoute (SplitGlobalInput L hL) W r) hre
  exact ⟨fun hY ↦ Set.disjoint_left.1 (havoid r) hends.1 hY,
    fun hY ↦ Set.disjoint_left.1 (havoid r) hends.2 hY⟩

/-- When inserted forward edges avoid a limiting-ladder component, every
repaired edge entering that component already has its tail on the same
component. -/
private theorem split_repairedEdge_tail_mem_of_head_mem_of_forward_avoids
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (W : Popular.XSWarp
      (SplitGlobalInput L hL).lambda (SplitGlobalInput L hL).lambda.target)
    {Y : Gamma.DPath} (hY : Y ∈ L.limitWarp)
    (hforward : ∀ e ∈ canonicalErasedForwardEdges
      (SplitGlobalInput L hL) W,
      e.1 ∉ Y.support ∧ e.2 ∉ Y.support)
    {x y : V} (hy : y ∈ Y.support)
    (hxy : (x, y) ∈ canonicalErasedRepairedEdges
      (SplitGlobalInput L hL) W) :
    x ∈ Y.support := by
  rcases hxy with hbase | hinserted
  · obtain ⟨Z, hZ, hxyZ⟩ := hbase.1.1
    have hyZ : y ∈ Z.support := (Z.edgeSet_subset_support_prod hxyZ).2
    have hYZ : Y = Z :=
      Alternating.DWeb.IsWarp.eq_of_mem_support
        (hL.legal.warpStages (Ladder.finalStage kappa))
        hY hZ hy hyZ
    rw [hYZ]
    exact (Z.edgeSet_subset_support_prod hxyZ).1
  · exact False.elim ((hforward (x, y) hinserted).2 hy)

/-- A repaired-relation root of a point on an untouched component must lie
on that component. -/
private theorem split_root_mem_support_of_reaches_of_forward_avoids
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (W : Popular.XSWarp
      (SplitGlobalInput L hL).lambda (SplitGlobalInput L hL).lambda.target)
    {Y : Gamma.DPath} (hY : Y ∈ L.limitWarp)
    (hforward : ∀ e ∈ canonicalErasedForwardEdges
      (SplitGlobalInput L hL) W,
      e.1 ∉ Y.support ∧ e.2 ∉ Y.support)
    {a b : V}
    (hab : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
        (SplitGlobalInput L hL) W) a b)
    (hb : b ∈ Y.support) :
    a ∈ Y.support := by
  induction hab with
  | refl => exact hb
  | @tail x y hax hxy ih =>
      apply ih
      exact split_repairedEdge_tail_mem_of_head_mem_of_forward_avoids
        L hL W hY hforward hb hxy

/-- Machine-checked obstruction for the untouched-hanging alternative:
its terminal has no original-source root in the strict selected repaired
relation. -/
theorem SplitReservedStationaryEqualSelection.not_sourceRooted_terminal_of_untouchedHanging
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {P : Popular.XSWarp
      (SplitGlobalInput L hL).lambda (SplitGlobalInput L hL).lambda.target}
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (Y : Gamma.DPath)
    (hY : Y ∈ Gamma.essentialWarpPart L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y)
    (havoid : ∀ r : WarpPath S.strictRoutes,
      Disjoint
        (canonicalErasedRoute (SplitGlobalInput L hL) S.strictRoutes r).vertexSet
        Y.support)
    {b : V} (hterminal : Y.terminal? = some b) :
    ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (SplitGlobalInput L hL) S.strictRoutes) a b := by
  intro hroot
  obtain ⟨a, haSource, hab⟩ := hroot
  have hforward : ∀ e ∈ canonicalErasedForwardEdges
      (SplitGlobalInput L hL) S.strictRoutes,
      e.1 ∉ Y.support ∧ e.2 ∉ Y.support := by
    intro e he
    exact split_forwardEdges_endpoints_not_mem_of_route_disjoint
      S.strictRoutes Y havoid he
  have hbSupport : b ∈ Y.support := Gamma.terminal_mem_support hterminal
  have haSupport : a ∈ Y.support :=
    split_root_mem_support_of_reaches_of_forward_avoids
      L hL S.strictRoutes hY.1 hforward hab hbSupport
  exact Set.disjoint_left.1
    (split_support_disjoint_source_of_hanging Y hNoEnter hhang)
    haSupport haSource

/-- Exact failure of the proposed untouched-hanging dispatcher.  Even when
the terminal has an ambient finite path from the source (as it does on the
reachable terminal cut), it is neither rooted in the strict repaired
relation nor contacted by a strict route.  A separate maximality theorem is
therefore required to rule this branch out. -/
theorem SplitReservedStationaryEqualSelection.untouchedHanging_not_absorbable
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {P : Popular.XSWarp
      (SplitGlobalInput L hL).lambda (SplitGlobalInput L hL).lambda.target}
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (Y : Gamma.DPath)
    (hY : Y ∈ Gamma.essentialWarpPart L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y)
    (havoid : ∀ r : WarpPath S.strictRoutes,
      Disjoint
        (canonicalErasedRoute (SplitGlobalInput L hL) S.strictRoutes r).vertexSet
        Y.support)
    {b : V} (hterminal : Y.terminal? = some b)
    (_hambient : ∃ p : FinitePath Gamma.graph,
      p.start ∈ Gamma.source ∧ p.finish = b) :
    ¬ ((∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (SplitGlobalInput L hL) S.strictRoutes) a b) ∨
      ∃ r : WarpPath S.strictRoutes,
        ((canonicalErasedRoute
            (SplitGlobalInput L hL) S.strictRoutes r).vertexSet ∩
          Y.support).Nonempty) := by
  rintro (hroot | hcontact)
  · exact S.not_sourceRooted_terminal_of_untouchedHanging
      hNoEnter Y hY hhang havoid hterminal hroot
  · obtain ⟨r, x, hxr, hxY⟩ := hcontact
    exact Set.disjoint_left.1 (havoid r) hxr hxY

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.SplitReservedStationaryEqualSelection.not_sourceRooted_terminal_of_untouchedHanging
#print axioms Erdos599.DWeb.KappaLadder.SplitReservedStationaryEqualSelection.untouchedHanging_not_absorbable
