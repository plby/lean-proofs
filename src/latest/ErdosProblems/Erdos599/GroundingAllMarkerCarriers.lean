/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerIncidence
import ErdosProblems.Erdos599.PopularSourceCarrierCut

/-!
# Source-reachable record carriers in the all-marker auxiliary

A record carrier consists of its source and exactly its reference-edge
gadgets. Different records have disjoint carriers. A finite record reaches
its gadgets by backwards identity steps from its terminal; a ray proxy
reaches any one of its gadgets directly using that original ray edge.
Loop erasure converts the concrete walks into finite paths inside the
same carrier. This discharges the hypotheses of the existing carrier-cut
nonstationarity theorem.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u v

variable {V : Type u} {I : Type v} {G : DWeb V} (L : Input G I)

def recordCarrier (i : I) : Set L.Vertex
  | .source j => j = i
  | .marker _ => False
  | .edge e => e.1 ∈ (L.record i).edgeSet
  | .off _ => False

theorem recordCarrier_disjoint : Pairwise (fun i j ↦
    Disjoint (L.recordCarrier i) (L.recordCarrier j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro a hai haj
  cases a with
  | source k => exact hij (hai.symm.trans haj)
  | marker y => exact hai.elim
  | off x => exact hai.elim
  | edge e =>
      have hpaths : L.record i = L.record j :=
        DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
          (L.record_mem i) (L.record_mem j)
          ((L.record i).edgeSet_subset_support_prod hai).1
          ((L.record j).edgeSet_subset_support_prod haj).1
      exact hij (L.record_injective hpaths)

private theorem append_one_in_carrier (i : I) {a b : L.Vertex}
    (w : Walk L.web.graph (.source i) a)
    (hw : ∀ z ∈ w.support, z ∈ L.recordCarrier i)
    (hab : L.web.graph.Adj a b) (hb : b ∈ L.recordCarrier i) :
    ∃ q : Walk L.web.graph (.source i) b,
      ∀ z ∈ q.support, z ∈ L.recordCarrier i := by
  refine ⟨w.append (.cons hab .nil), ?_⟩
  intro z hz
  simp only [Walk.support_append, Walk.support_cons, Walk.support_nil,
    List.tail_cons, List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact hw z hz
  · exact hb

/-- Backwards traversal of any finite suffix whose edges belong to the
record, starting from its terminal sending port. Simplicity is not needed
until the final loop erasure. -/
private theorem backward_carrier_walk (i : I) {a b : V}
    (w : Walk G.graph a b) :
    L.sending (.source i) = some b → w.edgeSet ⊆ (L.record i).edgeSet →
    ∀ (e : {e : V × V // e ∈ familyEdges L.reference.paths}), e.1 ∈ w.edgeSet →
      ∃ q : Walk L.web.graph (.source i) (.edge e),
        ∀ z ∈ q.support, z ∈ L.recordCarrier i := by
  induction w with
  | nil =>
      intro _ _ e he
      exact he.elim
  | @cons a c b hac w ih =>
      intro hb hEdges e he
      simp only [Walk.edgeSet, Set.mem_union, Set.mem_singleton_iff] at he
      rcases he with heHead | heTail
      · have heRecord : e.1 ∈ (L.record i).edgeSet := hEdges (Or.inl heHead)
        have heReceive : L.receiving (.edge e) = some c := by
          simp only [receiving, heHead]
        cases w with
        | nil =>
            have hedge : L.web.graph.Adj (.source i) (.edge e) :=
              L.adj_of_original_or_identity hb heReceive (by intro h; cases h) (Or.inr rfl)
            apply L.append_one_in_carrier i .nil ?_ hedge heRecord
            intro z hz
            have hzi : z = .source i := by
              simpa only [Walk.support_nil, List.mem_singleton] using hz
            subst z
            exact rfl
        | @cons _ d _ hcd tail =>
            have htailEdges : (Walk.cons hcd tail).edgeSet ⊆ (L.record i).edgeSet :=
              fun _ h ↦ hEdges (Or.inr h)
            let f : {e : V × V // e ∈ familyEdges L.reference.paths} :=
              ⟨(c, d), by
                simp only [familyEdges, Set.mem_iUnion]
                exact ⟨L.record i, L.record_mem i, htailEdges (Or.inl rfl)⟩⟩
            obtain ⟨q, hq⟩ := ih hb htailEdges f (Or.inl rfl)
            by_cases hfe : (Vertex.edge f : L.Vertex) = .edge e
            · have hfe' : f = e := Vertex.edge.inj hfe
              subst e
              exact ⟨q, hq⟩
            · have hedge : L.web.graph.Adj (.edge f) (.edge e) :=
                L.adj_of_original_or_identity (by rfl) heReceive hfe (Or.inr rfl)
              exact L.append_one_in_carrier i q hq hedge heRecord
      · exact ih hb (fun _ h ↦ hEdges (Or.inr h)) e heTail

/-- Every carrier vertex is reached from the record source by a concrete
finite path wholly inside its carrier. -/
theorem recordCarrier_internally_reachable (i : I) (a : L.Vertex)
    (ha : a ∈ L.recordCarrier i) :
    ∃ p : FinitePath L.web.graph,
      p.start = .source i ∧ p.finish = a ∧ p.support ⊆ L.recordCarrier i := by
  have hwalk : ∃ w : Walk L.web.graph (.source i) a,
      ∀ z ∈ w.support, z ∈ L.recordCarrier i := by
    cases a with
    | source j =>
        change j = i at ha
        subst j
        refine ⟨.nil, ?_⟩
        intro z hz
        have hzi : z = .source i := by simpa only [Walk.support_nil, List.mem_singleton] using hz
        subst z
        exact rfl
    | marker y => exact ha.elim
    | off x => exact ha.elim
    | edge e =>
        change e.1 ∈ (L.record i).edgeSet at ha
        cases hi : L.record i with
        | inl f =>
            apply L.backward_carrier_walk i f.walk
            · simp only [sending, hi, Path.terminal?]
            · intro v hv
              simpa only [hi, Path.edgeSet, FinitePath.edgeSet] using hv
            · simpa only [hi, Path.edgeSet, FinitePath.edgeSet] using ha
        | inr r =>
            have heRay : e.1 ∈ r.edgeSet := by simpa only [hi, Path.edgeSet] using ha
            have hedge : L.web.graph.Adj (.source i) (.edge e) := by
              refine ⟨?_, e.1.2, rfl, Or.inr ⟨i, r, rfl, hi, ?_⟩⟩
              · intro h
                cases h
              · exact ⟨e.1.1, (r.edgeSet_subset_support_prod heRay).1, r.edgeSet_subset_adj heRay⟩
            apply L.append_one_in_carrier i .nil ?_ hedge ha
            intro z hz
            have hzi : z = .source i := by
              simpa only [Walk.support_nil, List.mem_singleton] using hz
            subst z
            exact rfl
  obtain ⟨w, hw⟩ := hwalk
  obtain ⟨q, hq⟩ := RelationalRoof.exists_pathTo_support_subset
    (R := L.web.graph.Adj) w
  exact ⟨⟨.source i, a, q.1, q.2⟩, rfl, rfl, fun _ hz ↦ hw _ (hq hz)⟩

def sourceCarriers : Popular.SourceCarrierFamily L.web where
  carrier x := L.recordCarrier (L.sourceEquiv.symm x)
  disjoint := by
    intro x y hxy
    exact L.recordCarrier_disjoint (fun h ↦ hxy (L.sourceEquiv.symm.injective h))
  internally_reachable := by
    intro x a ha
    obtain ⟨p, hp, hpa, hsupport⟩ :=
      L.recordCarrier_internally_reachable (L.sourceEquiv.symm x) a ha
    exact ⟨p, hp.trans (L.sourceEquiv_symm_val x), hpa, hsupport⟩

#print axioms recordCarrier_internally_reachable
#print axioms sourceCarriers

end Erdos599.GroundingAllMarkerAuxiliary.Input
