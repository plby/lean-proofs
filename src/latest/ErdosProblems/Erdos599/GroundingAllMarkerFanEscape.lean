/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerGoodFans

/-!
# Internal normalized fan ports cannot escape to uncut markers

First-hit prefixes to internal vertices avoid the cut. A residual escape
from a represented internal sending or receiving port would recontract to
a cut-avoiding auxiliary route to an uncut marker. Concatenating with the
prefix contradicts the actual auxiliary separator. In particular no fan
path meets an internal edge gadget of an uncut-marker initial fragment.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}

theorem normalizedRequestFan_internal_not_cut {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.normalizedRequestFan S r).paths)
    {a : L.Vertex} (ha : a ∈ p.support) (har : a ≠ r.1) : a ∉ S.cut :=
  fun haC ↦ har (L.normalizedRequestFan_cut_normalized S r hp ⟨ha, haC⟩)

theorem normalizedRequestFan_prefix_to_internal {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.normalizedRequestFan S r).paths)
    {a : L.Vertex} (ha : a ∈ p.support) (har : a ≠ r.1) :
    L.CutAvoidingWalk S.cut p.start a := by
  have hmeet : p.walk.Meets ({a} : Set L.Vertex) := ⟨a, ha, rfl⟩
  let q := p.firstHit {a} hmeet
  have hfinish : q.finish = a := p.firstHit_finish_mem {a} hmeet
  have hav : ∀ z ∈ q.walk.support, z ∉ S.cut := by
    intro z hz hzC
    have hzr : z = r.1 := L.normalizedRequestFan_cut_normalized S r hp
      ⟨p.firstHit_support_subset {a} hmeet hz, hzC⟩
    have hrfinish := L.normalizedRequestFan_finish S r hp
    have hnot : p.finish ∉ ({a} : Set L.Vertex) := by
      rw [hrfinish]
      exact fun h ↦ har h.symm
    exact Popular.firstHit_not_mem_of_finish_not_mem p {a} hmeet hnot
      ((hzr.trans hrfinish.symm) ▸ hz)
  have hq : L.CutAvoidingWalk S.cut q.start q.finish := ⟨q.walk, hav⟩
  exact hfinish ▸ hq

/-- An auxiliary source-to-cut route cannot have an internal sending port
which reaches an uncut marker in the cut-residual graph. -/
theorem normalizedRequestFan_sending_not_escape {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.normalizedRequestFan S r).paths)
    {a : L.Vertex} (ha : a ∈ p.support) (har : a ≠ r.1) {x : V}
    (hsend : L.sending a = some x) : ¬ L.Escapes S.cut (.inl x) := by
  intro hescape
  obtain ⟨y, hay⟩ := L.cutAvoidingWalk_of_sending_escape S.cut hsend
    (L.normalizedRequestFan_internal_not_cut S r hp ha har) hescape
  have hwalk := L.cutAvoidingWalk_trans S.cut
    (L.normalizedRequestFan_prefix_to_internal S r hp ha har) hay
  obtain ⟨i, hi⟩ := (L.normalizedRequestFan S r).starts_in_source hp
  apply L.not_cutAvoidingWalk_source_marker S.cut S.separates i y
  simpa only [hi] using hwalk

theorem normalizedRequestFan_receiving_not_escape {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.normalizedRequestFan S r).paths)
    {a : L.Vertex} (ha : a ∈ p.support) (har : a ≠ r.1) {x : V}
    (hreceive : L.receiving a = some x) : ¬ L.Escapes S.cut (.inr x) := by
  rintro ⟨y, hy, ⟨w⟩⟩
  obtain ⟨b, hb, _hbC, hby⟩ := L.escapeEncoding_of_walk S.cut y hy w
  have hab : a = b := L.receiving_unique hreceive hb
  have hay : L.CutAvoidingWalk S.cut a (.marker y) := hab ▸ hby
  have hwalk := L.cutAvoidingWalk_trans S.cut
    (L.normalizedRequestFan_prefix_to_internal S r hp ha har) hay
  obtain ⟨i, hi⟩ := (L.normalizedRequestFan S r).starts_in_source hp
  apply L.not_cutAvoidingWalk_source_marker S.cut S.separates i y
  simpa only [hi] using hwalk

/-- These are precisely the gadgets of surviving edges belonging to the
fragment, not all gadgets anywhere on its original parent. -/
def fragmentEdgeVertices (P : L.CutFragment) : Set L.Vertex
  | .edge e => e.1 ∈ P.path.edgeSet
  | _ => False

theorem fragmentEdgeVertices_disjoint_cut (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) : Disjoint (L.fragmentEdgeVertices P) C := by
  apply Set.disjoint_left.mpr
  intro a ha haC
  cases a with
  | source i => exact ha.elim
  | marker y => exact ha.elim
  | off x => exact ha.elim
  | edge e => exact Set.disjoint_left.mp (L.cutFragment_edges_disjoint C hP) ha ⟨e.2, haC⟩

/-- Nonattachable hanging fragments do not occur in a normalized fan at
all: even one of their surviving edge gadgets would supply an escape. -/
theorem normalizedRequestFan_avoids_uncut_marker_fragment
    {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
    (r : L.Request S.cut) {p : FinitePath L.web.graph}
    (hp : p ∈ (L.normalizedRequestFan S r).paths) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments S.cut) (y : L.markers) (hy : Vertex.marker y ∉ S.cut)
    (hinitial : P.path.initial = y.1) : Disjoint p.support (L.fragmentEdgeVertices P) := by
  apply Set.disjoint_left.mpr
  intro a hap haP
  have haC : a ∉ S.cut := Set.disjoint_left.mp (L.fragmentEdgeVertices_disjoint_cut S.cut hP) haP
  have har : a ≠ r.1 := fun h ↦ haC (h ▸ r.2.1)
  cases a with
  | source i => exact haP.elim
  | marker m => exact haP.elim
  | off x => exact haP.elim
  | edge e =>
      have hxR := L.cutFragment_subset_escapeRegion_of_uncut_marker_initial
        S.cut hP y hy hinitial (P.path.edgeSet_subset_support_prod haP).1
      exact L.normalizedRequestFan_sending_not_escape S r hp hap har rfl hxR

theorem goodRecordFan_avoids_uncut_marker_fragment
    {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
    (r : L.Request S.cut) {p : FinitePath L.web.graph}
    (hp : p ∈ (L.goodRecordFan S r).paths) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments S.cut) (y : L.markers) (hy : Vertex.marker y ∉ S.cut)
    (hinitial : P.path.initial = y.1) : Disjoint p.support (L.fragmentEdgeVertices P) :=
  L.normalizedRequestFan_avoids_uncut_marker_fragment S r
    (L.goodRecordFan_subset_normalized S r hp) hP y hy hinitial

#print axioms normalizedRequestFan_prefix_to_internal
#print axioms normalizedRequestFan_sending_not_escape
#print axioms normalizedRequestFan_receiving_not_escape
#print axioms goodRecordFan_avoids_uncut_marker_fragment

end Erdos599.GroundingAllMarkerAuxiliary.Input
