/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerFanEscape

/-!
# Literal backwards walks between all-marker port representatives

A finite reference interval can be traversed backwards in the actual
auxiliary graph. The support consists only of its edge gadgets and the
chosen sending and receiving representatives. This gives the internal
continuations needed by first-contact pruning, including cut-marker and
cut-edge endpoints, without using an older auxiliary graph.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

/-- Reverse a reference walk while staying in any set containing its
edge gadgets and the two endpoint representatives. -/
theorem backward_representative_walk (D : Set L.Vertex) {x y : V}
    (w : Walk G.graph x y)
    (hEdges : w.edgeSet ⊆ familyEdges L.reference.paths)
    (hGadgets : ∀ e : {e : V × V // e ∈ familyEdges L.reference.paths},
      e.1 ∈ w.edgeSet → Vertex.edge e ∈ D)
    {a b : L.Vertex} (ha : L.sending a = some y) (hb : L.receiving b = some x)
    (haD : a ∈ D) (hbD : b ∈ D) :
    ∃ q : Walk L.web.graph a b, ∀ z ∈ q.support, z ∈ D := by
  induction w generalizing a b with
  | nil =>
      by_cases hab : a = b
      · subst b
        refine ⟨.nil, ?_⟩
        intro z hz
        have hza : z = a := by simpa only [Walk.support_nil, List.mem_singleton] using hz
        exact hza ▸ haD
      · have habEdge := L.adj_of_original_or_identity ha hb hab (Or.inr rfl)
        refine ⟨.cons habEdge .nil, ?_⟩
        intro z hz
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact haD
        · exact hbD
  | @cons x z y hxz w ih =>
      let e : {e : V × V // e ∈ familyEdges L.reference.paths} :=
        ⟨(x, z), hEdges (Or.inl rfl)⟩
      have heD : Vertex.edge e ∈ D := hGadgets e (Or.inl rfl)
      obtain ⟨q, hq⟩ := ih (fun _ he ↦ hEdges (Or.inr he))
        (fun e he ↦ hGadgets e (Or.inr he)) ha (show L.receiving (.edge e) = some z from rfl)
        haD heD
      by_cases heb : Vertex.edge e = b
      · subst b
        exact ⟨q, hq⟩
      · have habEdge : L.web.graph.Adj (.edge e) b :=
          L.adj_of_original_or_identity rfl hb heb (Or.inr rfl)
        refine ⟨q.append (.cons habEdge .nil), ?_⟩
        intro t ht
        simp only [Walk.support_append, Walk.support_cons, Walk.support_nil,
          List.tail_cons, List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact hq t ht
        · exact hbD

/-- A gadget on a fragment reaches any representative receiving at the
fragment's initial, using only fragment gadgets and that representative. -/
theorem fragmentEdgeVertices_continuation (P : L.CutFragment) {b : L.Vertex}
    (hb : L.receiving b = some P.path.initial) {a : L.Vertex}
    (ha : a ∈ L.fragmentEdgeVertices P) :
    ∃ q : FinitePath L.web.graph, q.start = a ∧ q.finish = b ∧
      q.support ⊆ L.fragmentEdgeVertices P ∪ {b} := by
  cases a with
  | source i => exact ha.elim
  | marker y => exact ha.elim
  | off x => exact ha.elim
  | edge e =>
      have hx : e.1.1 ∈ P.path.support := (P.path.edgeSet_subset_support_prod ha).1
      have hinterval : ∃ q : FinitePath G.graph,
          q.start = P.path.initial ∧ q.finish = e.1.1 ∧ q.edgeSet ⊆ P.path.edgeSet := by
        by_cases hxi : P.path.initial = e.1.1
        · refine ⟨⟨P.path.initial, P.path.initial, .nil, by simp⟩, rfl, hxi, ?_⟩
          exact Set.empty_subset _
        · exact GroundingCutDecoder.exists_forward_segment_of_before
            ⟨GroundingFragmentWarp.initial_beforeEq_of_mem hx, hxi⟩
      obtain ⟨q, hqs, hqt, hqEdges⟩ := hinterval
      have hqFamily : q.walk.edgeSet ⊆ familyEdges L.reference.paths := by
        intro f hf
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨P.parent, P.parent_mem, P.edges_subset (hqEdges hf)⟩
      have hsend : L.sending (.edge e) = some q.finish := by
        change some e.1.1 = some q.finish
        rw [hqt]
      have hreceive : L.receiving b = some q.start := by simpa only [hqs] using hb
      obtain ⟨w, hw⟩ := L.backward_representative_walk
        (L.fragmentEdgeVertices P ∪ {b}) q.walk hqFamily
        (fun f hf ↦ Or.inl (hqEdges hf)) hsend hreceive (Or.inl ha) (Or.inr rfl)
      obtain ⟨r, hr⟩ := RelationalRoof.exists_pathTo_support_subset
        (R := L.web.graph.Adj) w
      exact ⟨⟨.edge e, b, r.1, r.2⟩, rfl, rfl, fun t ht ↦ hw t (hr ht)⟩

#print axioms backward_representative_walk
#print axioms fragmentEdgeVertices_continuation

end Erdos599.GroundingAllMarkerAuxiliary.Input
