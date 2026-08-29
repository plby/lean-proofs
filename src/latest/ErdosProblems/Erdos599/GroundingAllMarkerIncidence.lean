/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerAuxiliary
import ErdosProblems.Erdos599.WarpFamilyBoundary

/-!
# Exact incidence of contracted all-marker vertices

Each retained sending or receiving port belongs to exactly one auxiliary
vertex. The finite sources and marker targets are genuinely unmatched.
Matching ports belong to the same contracted vertex, so the ordinary
auxiliary edges omit precisely matching edges and loops, not additional
routes. These facts are used when converting separator avoidance back
and forth between the auxiliary and residual fragment graphs.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts
open Blueprint.LinkageBlueprint

universe u v

variable {V : Type u} {I : Type v} {G : DWeb V} (L : Input G I)

theorem source_sending_unmatched (i : I) {x : V}
    (hx : L.sending (.source i) = some x) :
    ∀ y, ¬ referenceMatching L.reference.paths x y := by
  intro y hy
  have hterminal : x ∈ G.terminalFrontier L.reference.paths :=
    ⟨L.record i, L.record_mem i, hx⟩
  rcases hy with he | ⟨_, hoff⟩
  · exact isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier
      L.reference.disjoint hterminal ⟨y, he⟩
  · exact hoff ⟨L.record i, L.record_mem i, G.terminal_mem_support hx⟩

theorem marker_receiving_unmatched (y : L.markers) :
    ∀ x, ¬ referenceMatching L.reference.paths x y.1 := by
  intro x hx
  rcases hx with he | ⟨rfl, hoff⟩
  · exact isWarp_noIncoming_familyEdges_of_mem_initialSet
      L.reference.disjoint (L.markers_initial y.2) ⟨x, he⟩
  · obtain ⟨p, hp, hpy⟩ := L.markers_initial y.2
    exact hoff ⟨p, hp, hpy ▸ p.initial_mem_support⟩

/-- The receiving coordinate represents an actual port, with no duplicates
between marker targets, edge gadgets and off-reference identities. -/
theorem receiving_unique {a b : L.Vertex} {x : V}
    (ha : L.receiving a = some x) (hb : L.receiving b = some x) : a = b := by
  cases a with
  | source i => simp [receiving] at ha
  | marker y =>
      have hyx : y.1 = x := Option.some.inj ha
      cases b with
      | source i => simp [receiving] at hb
      | marker z =>
          exact congrArg Vertex.marker (Subtype.ext (hyx.trans (Option.some.inj hb).symm))
      | edge e =>
          have hey : e.1.2 = y.1 := (Option.some.inj hb).trans hyx.symm
          exact (L.marker_receiving_unmatched y e.1.1 (Or.inl (hey ▸ e.2))).elim
      | off z =>
          have hzy : z.1 = y.1 := (Option.some.inj hb).trans hyx.symm
          obtain ⟨p, hp, hpy⟩ := L.markers_initial y.2
          exact (z.2 ⟨p, hp, hzy.symm ▸ hpy ▸ p.initial_mem_support⟩).elim
  | edge e =>
      have hex : e.1.2 = x := Option.some.inj ha
      cases b with
      | source i => simp [receiving] at hb
      | marker y =>
          have hey : e.1.2 = y.1 := hex.trans (Option.some.inj hb).symm
          exact (L.marker_receiving_unmatched y e.1.1 (Or.inl (hey ▸ e.2))).elim
      | edge f =>
          have hef : e.1.2 = f.1.2 := hex.trans (Option.some.inj hb).symm
          have hleft : e.1.1 = f.1.1 :=
            (IsWarp.familyEdges_biUnique L.reference.disjoint).1 (hef ▸ e.2) f.2
          exact congrArg Vertex.edge (Subtype.ext (Prod.ext hleft hef))
      | off z =>
          have hez : e.1.2 = z.1 := hex.trans (Option.some.inj hb).symm
          exact (z.2 (hez ▸ (familyEdges_subset_vertexSet_prod L.reference.paths e.2).2)).elim
  | off z =>
      have hzx : z.1 = x := Option.some.inj ha
      cases b with
      | source i => simp [receiving] at hb
      | marker y =>
          have hzy : z.1 = y.1 := hzx.trans (Option.some.inj hb).symm
          obtain ⟨p, hp, hpy⟩ := L.markers_initial y.2
          exact (z.2 ⟨p, hp, hzy.symm ▸ hpy ▸ p.initial_mem_support⟩).elim
      | edge e =>
          have hez : e.1.2 = z.1 := (Option.some.inj hb).trans hzx.symm
          exact (z.2 (hez ▸ (familyEdges_subset_vertexSet_prod L.reference.paths e.2).2)).elim
      | off w =>
          exact congrArg Vertex.off (Subtype.ext (hzx.trans (Option.some.inj hb).symm))

/-- A represented sending port is either a finite record terminal or
belongs to one of the contracted matching vertices. -/
theorem sending_cases {a : L.Vertex} {x : V}
    (ha : L.sending a = some x) :
    (∃ i, a = .source i) ∨
      ∃ y, L.receiving a = some y ∧ referenceMatching L.reference.paths x y := by
  cases a with
  | source i => exact Or.inl ⟨i, rfl⟩
  | marker y => simp [sending] at ha
  | edge e =>
      exact Or.inr ⟨e.1.2, rfl, Or.inl ((Option.some.inj ha) ▸ e.2)⟩
  | off z =>
      have hzx : z.1 = x := Option.some.inj ha
      exact Or.inr ⟨z.1, rfl, Or.inr ⟨hzx.symm, hzx ▸ z.2⟩⟩

/-- Sending ports also have unique owners, including finite record
sources. Record injectivity and reference-warp disjointness are essential
in the source-source case. -/
theorem sending_unique {a b : L.Vertex} {x : V}
    (ha : L.sending a = some x) (hb : L.sending b = some x) : a = b := by
  rcases L.sending_cases ha with ⟨i, rfl⟩ | ⟨y, hay, hxy⟩
  · rcases L.sending_cases hb with ⟨j, rfl⟩ | ⟨z, _, hxz⟩
    · have hrec : L.record i = L.record j :=
        DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
          (L.record_mem i) (L.record_mem j)
          (G.terminal_mem_support ha) (G.terminal_mem_support hb)
      exact congrArg Vertex.source (L.record_injective hrec)
    · exact (L.source_sending_unmatched i ha z hxz).elim
  · rcases L.sending_cases hb with ⟨j, rfl⟩ | ⟨z, hbz, hxz⟩
    · exact (L.source_sending_unmatched j hb y hxy).elim
    · have hyz : y = z :=
        (referenceMatching_biUnique L.reference.disjoint).2 hxy hxz
      exact L.receiving_unique (hyz ▸ hay) hbz

/-- Matching pairs are exactly the two ports of one retained contracted
vertex. In particular finite source ports cannot be silently contracted. -/
theorem referenceMatching_iff_same_vertex {a b : L.Vertex} {x y : V}
    (ha : L.sending a = some x) (hb : L.receiving b = some y) :
    referenceMatching L.reference.paths x y ↔ a = b := by
  constructor
  · intro hxy
    cases a with
    | source i => exact (L.source_sending_unmatched i ha y hxy).elim
    | marker z => simp [sending] at ha
    | edge e =>
        have hex : e.1.1 = x := Option.some.inj ha
        have hmatch : referenceMatching L.reference.paths x e.1.2 := Or.inl (hex ▸ e.2)
        have hey : e.1.2 = y :=
          (referenceMatching_biUnique L.reference.disjoint).2 hmatch hxy
        exact L.receiving_unique (by exact congrArg some hey) hb
    | off z =>
        have hzx : z.1 = x := Option.some.inj ha
        have hmatch : referenceMatching L.reference.paths x z.1 :=
          Or.inr ⟨hzx.symm, hzx ▸ z.2⟩
        have hzy : z.1 = y :=
          (referenceMatching_biUnique L.reference.disjoint).2 hmatch hxy
        exact L.receiving_unique (by exact congrArg some hzy) hb
  · rintro rfl
    exact L.internal_step ha hb

/-- Every original or identity non-loop connection between represented
ports is an auxiliary edge; the contraction has discarded no such route. -/
theorem adj_of_original_or_identity {a b : L.Vertex} {x y : V}
    (ha : L.sending a = some x) (hb : L.receiving b = some y)
    (hne : a ≠ b) (hxy : G.graph.Adj x y ∨ x = y) : L.web.graph.Adj a b := by
  refine ⟨hne, y, hb, Or.inl ⟨x, ha, hxy, ?_⟩⟩
  intro hmatch
  exact hne ((L.referenceMatching_iff_same_vertex ha hb).mp hmatch)

#print axioms receiving_unique
#print axioms sending_unique
#print axioms referenceMatching_iff_same_vertex
#print axioms adj_of_original_or_identity

end Erdos599.GroundingAllMarkerAuxiliary.Input
