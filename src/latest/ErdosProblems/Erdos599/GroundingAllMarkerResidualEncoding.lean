/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerResidual

/-!
# Recontracting successful cut-residual escapes

A successful escape from a receiving port has an uncut auxiliary owner.
From a sending port we require a supplied uncut owner, since other unmatched
sending ports were deliberately omitted from the auxiliary. This asymmetric
invariant handles the free cut tails and dead cut heads without inventing
vertices or treating a removed matching edge as an old nonmatching edge.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

def CutAvoidingWalk (C : Set L.Vertex) (a b : L.Vertex) : Prop :=
  ∃ w : Walk L.web.graph a b, ∀ z ∈ w.support, z ∉ C

theorem cutAvoidingWalk_nil (C : Set L.Vertex) {a : L.Vertex}
    (ha : a ∉ C) : L.CutAvoidingWalk C a a := by
  refine ⟨.nil, ?_⟩
  simpa only [Walk.support_nil, List.mem_singleton] using
    (fun z (hz : z = a) ↦ hz ▸ ha)

theorem cutAvoidingWalk_cons (C : Set L.Vertex) {a b c : L.Vertex}
    (ha : a ∉ C) (hab : L.web.graph.Adj a b)
    (hbc : L.CutAvoidingWalk C b c) : L.CutAvoidingWalk C a c := by
  obtain ⟨w, hw⟩ := hbc
  refine ⟨.cons hab w, ?_⟩
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact ha
  · exact hw z hz

def EscapeEncoding (C : Set L.Vertex) (y : L.markers) : Port V → Prop
  | .inl x => ∀ a : L.Vertex, L.sending a = some x → a ∉ C →
      L.CutAvoidingWalk C a (.marker y)
  | .inr x => ∃ a : L.Vertex, L.receiving a = some x ∧ a ∉ C ∧
      L.CutAvoidingWalk C a (.marker y)

/-- All vertices in the contracted witness avoid the actual auxiliary cut. -/
theorem escapeEncoding_of_walk (C : Set L.Vertex) (y : L.markers)
    (hy : Vertex.marker y ∉ C) {p : Port V}
    (w : Walk (L.residualGraph C) p (.inr y.1)) : L.EscapeEncoding C y p := by
  generalize ht : (Sum.inr y.1 : Port V) = t at w
  induction w with
  | nil =>
      cases ht
      exact ⟨.marker y, rfl, hy, L.cutAvoidingWalk_nil C hy⟩
  | @cons p q r e w ih =>
      have ih' := ih ht
      cases p with
      | inl x =>
          cases q with
          | inl z => exact False.elim e
          | inr z =>
              obtain ⟨b, hb, hbC, hwalk⟩ := ih'
              intro a ha haC
              have hne : a ≠ b := by
                intro heq
                have hmatch : referenceMatching L.reference.paths x z :=
                  (L.referenceMatching_iff_same_vertex ha hb).mpr heq
                exact e.2.2.2 (L.referenceMatching_residual_of_receiver_uncut C hb hbC hmatch)
              exact L.cutAvoidingWalk_cons C haC
                (L.adj_of_original_or_identity ha hb hne e.2.2.1) hwalk
      | inr z =>
          cases q with
          | inl x =>
              obtain ⟨a, ha, hb, haC⟩ := L.exists_uncut_matchingVertex C e.2.2 e.2.1
              exact ⟨a, hb, haC, ih' a ha haC⟩
          | inr x => exact False.elim e

theorem cutAvoidingWalk_of_sending_escape (C : Set L.Vertex)
    {a : L.Vertex} {x : V} (ha : L.sending a = some x) (haC : a ∉ C)
    (hx : L.Escapes C (.inl x)) :
    ∃ y : L.markers, L.CutAvoidingWalk C a (.marker y) := by
  obtain ⟨y, hy, ⟨w⟩⟩ := hx
  exact ⟨y, L.escapeEncoding_of_walk C y hy w a ha haC⟩

/-- Loop erasure preserves avoidance and supplies the path required by
the separator definition. -/
theorem not_cutAvoidingWalk_source_marker (C : Set L.Vertex)
    (hC : Popular.IsSeparator L.web C) (i : I) (y : L.markers) :
    ¬ L.CutAvoidingWalk C (.source i) (.marker y) := by
  rintro ⟨w, hw⟩
  obtain ⟨q, hq⟩ := RelationalRoof.exists_pathTo_support_subset
    (R := L.web.graph.Adj) w
  let p : FinitePath L.web.graph := ⟨.source i, .marker y, q.1, q.2⟩
  obtain ⟨z, hz, hzC⟩ := hC p ⟨i, rfl⟩ ⟨y, rfl⟩
  exact hw z (hq hz) hzC

theorem not_escapes_of_source_sending (C : Set L.Vertex)
    (hC : Popular.IsSeparator L.web C) {i : I}
    (hiC : Vertex.source i ∉ C) {x : V}
    (hi : L.sending (.source i) = some x) : ¬ L.Escapes C (.inl x) := by
  intro hx
  obtain ⟨y, hw⟩ := L.cutAvoidingWalk_of_sending_escape C hi hiC hx
  exact L.not_cutAvoidingWalk_source_marker C hC i y hw

theorem not_escapes_finite_record_terminal (C : Set L.Vertex)
    (hC : Popular.IsSeparator L.web C) {i : I}
    (hiC : Vertex.source i ∉ C) (f : FinitePath G.graph)
    (hi : L.record i = .inl f) : ¬ L.Escapes C (.inl f.finish) := by
  apply L.not_escapes_of_source_sending C hC hiC
  simp only [sending, hi, Path.terminal?]

/-- A proxy can use any actual original departure from its ray. Its
receiving continuation is recontracted without a fabricated ray terminal. -/
theorem not_escapes_after_ray_departure (C : Set L.Vertex)
    (hC : Popular.IsSeparator L.web C) {i : I}
    (hiC : Vertex.source i ∉ C) (r : Ray G.graph) (hi : L.record i = .inr r)
    {x z : V} (hx : x ∈ r.support) (hxz : G.graph.Adj x z) :
    ¬ L.Escapes C (.inr z) := by
  rintro ⟨y, hy, ⟨w⟩⟩
  obtain ⟨b, hb, hbC, hw⟩ := L.escapeEncoding_of_walk C y hy w
  have hne : Vertex.source i ≠ b := by
    intro heq
    subst b
    simp [receiving] at hb
  have he : L.web.graph.Adj (.source i) b :=
    ⟨hne, z, hb, Or.inr ⟨i, r, rfl, hi, x, hx, hxz⟩⟩
  exact L.not_cutAvoidingWalk_source_marker C hC i y
    (L.cutAvoidingWalk_cons C hiC he hw)

#print axioms escapeEncoding_of_walk
#print axioms not_cutAvoidingWalk_source_marker
#print axioms not_escapes_finite_record_terminal
#print axioms not_escapes_after_ray_departure

end Erdos599.GroundingAllMarkerAuxiliary.Input
