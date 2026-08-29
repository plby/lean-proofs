/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PopularAuxiliary
import ErdosProblems.Erdos599.PopularLayers

/-!
# From the popular separator to the Section 8 grounding data

This file is the interface between Aharoni--Berger Theorem 8.4 and the
grounding switch in Theorem 7.30.  A separator vertex of the auxiliary web
is either an old original vertex, a represented ladder edge, or a ray proxy.
Only old non-source vertices and represented edges create switch requests.
We tag those requests, prove that their auxiliary representatives lie in
`C \ X`, retain the local stationary fan supplied by Theorem 8.4, and prove
that the complete request family has cardinality at most `κ`.

No grounding conclusion is assumed here: all results are direct projections
or decodings of the popular-separator output.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace PopularGroundingBridge

open DirectedPath

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev LV (_L : PopularAuxiliary.Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-! ## The two kinds of grounding requests -/

/-- Old original vertices selected by an auxiliary cut. -/
def oldPart (L : PopularAuxiliary.Input Gamma I) (C : Set (LV L)) : Set V :=
  {x | PopularAuxiliary.Input.LambdaVertex.old x ∈ C}

/-- Ladder edges whose representing gadgets are selected by a cut. -/
def edgePart (L : PopularAuxiliary.Input Gamma I)
    (C : Set (LV L)) : Set (V × V) :=
  {e | PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2 ∈ C}

/-- Old cut vertices which are not old auxiliary sources. -/
def oldRequests (L : PopularAuxiliary.Input Gamma I) (C : Set (LV L)) :
    Set V :=
  oldPart L C \ L.finiteSource

/-- Represented ladder edges selected by the auxiliary cut. -/
def edgeRequests (L : PopularAuxiliary.Input Gamma I) (C : Set (LV L)) :
    Set (V × V) :=
  edgePart L C

/-- A tagged request remembers the auxiliary cut vertex which supplied it.
Keeping the tag avoids making an arbitrary choice when several ladder edges
have the same head. -/
abbrev Request (L : PopularAuxiliary.Input Gamma I) (C : Set (LV L)) :=
  oldRequests L C ⊕ edgeRequests L C

/-- The original vertex at which a request is applied.  An old gadget acts
at itself; an edge gadget `(u,v)` is entered at its head `v`. -/
def requestVertex {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)} :
    Request L C → V
  | .inl x => x.1
  | .inr e => e.1.2

/-- The auxiliary cut vertex represented by a request. -/
def requestAuxVertex {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)} :
    Request L C → LV L
  | .inl x => .old x.1
  | .inr e => .edge e.1.1 e.1.2

/-- The untagged control set used in the paper:
`(C_V \ X) ∪ {head(e) | e ∈ C_E}`. -/
def controlVertices (L : PopularAuxiliary.Input Gamma I)
    (C : Set (LV L)) : Set V :=
  Set.range (@requestVertex V I Gamma L C)

@[simp]
theorem requestAuxVertex_mem_cut
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)}
    (r : Request L C) : requestAuxVertex r ∈ C := by
  cases r with
  | inl x => exact x.2.1
  | inr e => exact e.2

@[simp]
theorem requestAuxVertex_not_mem_source
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)}
    (r : Request L C) : requestAuxVertex r ∉ L.lambda.source := by
  cases r with
  | inl x =>
      intro hx
      exact x.2.2 ((L.mem_lambda_source_old x.1).1 hx)
  | inr e =>
      exact L.not_mem_lambda_source_edge e.1.1 e.1.2

theorem requestAuxVertex_mem_cut_diff_source
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)}
    (r : Request L C) :
    requestAuxVertex r ∈ C \ L.lambda.source :=
  ⟨requestAuxVertex_mem_cut r, requestAuxVertex_not_mem_source r⟩

/-! ## Cardinality decoded from `C \ X` -/

/-- Old requests embed into the non-source part of the auxiliary cut. -/
def oldRequestEmbedding
    (L : PopularAuxiliary.Input Gamma I) (C : Set (LV L)) :
    oldRequests L C ↪ (C \ L.lambda.source : Set (LV L)) where
  toFun x := ⟨.old x.1, x.2.1,
    fun hx ↦ x.2.2 ((L.mem_lambda_source_old x.1).1 hx)⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact PopularAuxiliary.Input.LambdaVertex.old.inj
      (congrArg Subtype.val hxy)

/-- Edge requests embed into the non-source part of the auxiliary cut. -/
def edgeRequestEmbedding
    (L : PopularAuxiliary.Input Gamma I) (C : Set (LV L)) :
    edgeRequests L C ↪ (C \ L.lambda.source : Set (LV L)) where
  toFun e := ⟨.edge e.1.1 e.1.2, e.2,
    L.not_mem_lambda_source_edge e.1.1 e.1.2⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    have h := congrArg Subtype.val hef
    exact Prod.ext
      (PopularAuxiliary.Input.LambdaVertex.edge.inj h).1
      (PopularAuxiliary.Input.LambdaVertex.edge.inj h).2

/-- Remove the universe lift from the cardinal clause of a popular
separator. -/
theorem cut_diff_source_card_le
    {L : PopularAuxiliary.Input Gamma I} {κ : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda κ}
    (S : Popular.PopularSeparator U) :
    #(S.cut \ L.lambda.source : Set (LV L)) ≤ κ :=
  Cardinal.lift_le.1 S.card_diff_source

theorem oldRequests_card_le
    {L : PopularAuxiliary.Input Gamma I} {κ : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda κ}
    (S : Popular.PopularSeparator U) :
    #(oldRequests L S.cut) ≤ κ :=
  (Cardinal.mk_le_of_injective
    (oldRequestEmbedding L S.cut).injective).trans
      (cut_diff_source_card_le S)

theorem edgeRequests_card_le
    {L : PopularAuxiliary.Input Gamma I} {κ : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda κ}
    (S : Popular.PopularSeparator U) :
    #(edgeRequests L S.cut) ≤ κ :=
  (Cardinal.mk_le_of_injective
    (edgeRequestEmbedding L S.cut).injective).trans
      (cut_diff_source_card_le S)

/-- The tagged request family has size at most `κ`. -/
theorem requests_card_le
    {L : PopularAuxiliary.Input Gamma I} {κ : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda κ)
    (S : Popular.PopularSeparator U) :
    #(Request L S.cut) ≤ κ := by
  rw [Cardinal.mk_sum]
  simp only [Cardinal.lift_id]
  exact (add_le_add (oldRequests_card_le S) (edgeRequests_card_le S)).trans
    (Cardinal.add_eq_self U.uncountable.le).le

/-- Forgetting the tag cannot increase cardinality, so the paper's
untagged control set also has size at most `κ`. -/
theorem controlVertices_card_le
    {L : PopularAuxiliary.Input Gamma I} {κ : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda κ)
    (S : Popular.PopularSeparator U) :
    #(controlVertices L S.cut) ≤ κ :=
  Cardinal.mk_range_le.trans (requests_card_le U S)

/-! ## Local stationary fans attached to requests -/

/-- The local fan supplied by the first clause of Theorem 8.4 at the
auxiliary representative of a request. -/
def requestFan
    {L : PopularAuxiliary.Input Gamma I} {κ : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda κ}
    (S : Popular.PopularSeparator U) (r : Request L S.cut) :
    Popular.JoinedFamily L.lambda {requestAuxVertex r} :=
  Classical.choose <| (S.locally_popular (requestAuxVertex r)
    (requestAuxVertex_mem_cut r)).resolve_left
      (requestAuxVertex_not_mem_source r)

theorem requestFan_stationary
    {L : PopularAuxiliary.Input Gamma I} {κ : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda κ}
    (S : Popular.PopularSeparator U) (r : Request L S.cut) :
    Stationary.IsStationaryBelow κ
      (Popular.initialIndicesOf U (requestFan S r).paths
        (requestFan S r).starts_in_source) :=
  (Classical.choose_spec <| (S.locally_popular (requestAuxVertex r)
    (requestAuxVertex_mem_cut r)).resolve_left
      (requestAuxVertex_not_mem_source r)).1

theorem requestFan_support_subset
    {L : PopularAuxiliary.Input Gamma I} {κ : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda κ}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    {p : FinitePath L.lambda.graph} (hp : p ∈ (requestFan S r).paths) :
    p.support ⊆ L.lambda.strictRoof S.cut ∪ {requestAuxVertex r} :=
  (Classical.choose_spec <| (S.locally_popular (requestAuxVertex r)
    (requestAuxVertex_mem_cut r)).resolve_left
      (requestAuxVertex_not_mem_source r)).2 p hp

private theorem familyEdge_of_adj_to_edge
    (L : PopularAuxiliary.Input Gamma I) {a : LV L} {u v : V}
    (h : L.lambda.graph.Adj a (.edge u v)) :
    (u, v) ∈ L.familyEdges := by
  cases a with
  | old x => exact ((L.lambda_adj_old_edge x u v).1 h).1
  | edge r s => exact ((L.lambda_adj_edge_edge r s u v).1 h).2.1
  | proxy i => exact ((L.lambda_adj_proxy_edge i u v).1 h).1

private theorem Walk.exists_edge_to_of_mem_of_ne_start
    {W : Type u} {D : Digraph W} {a b z : W} (q : Walk D a b)
    (hz : z ∈ q.support) (hza : z ≠ a) :
    ∃ x, (x, z) ∈ q.edgeSet := by
  induction q with
  | nil => exact False.elim (hza (by simpa using hz))
  | @cons a c b h q ih =>
      simp only [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact False.elim (hza rfl)
      · by_cases hzc : z = c
        · exact ⟨a, by simp [hzc]⟩
        · obtain ⟨x, hx⟩ := ih hz hzc
          exact ⟨x, by simp [hx]⟩

private theorem edgeNode_mem_familyEdges_of_start_in_source
    (L : PopularAuxiliary.Input Gamma I)
    (p : FinitePath L.lambda.graph) (hstart : p.start ∈ L.lambda.source)
    {u v : V} (huv : PopularAuxiliary.Input.LambdaVertex.edge u v ∈ p.support) :
    (u, v) ∈ L.familyEdges := by
  have hne : (PopularAuxiliary.Input.LambdaVertex.edge u v : LV L) ≠
      p.start := by
    intro h
    exact L.not_mem_lambda_source_edge u v (h ▸ hstart)
  obtain ⟨a, ha⟩ := Walk.exists_edge_to_of_mem_of_ne_start p.walk huv hne
  exact familyEdge_of_adj_to_edge L (p.edgeSet_subset_adj ha)

/-- Every edge request really is an edge of the limiting ladder warp.  This
is decoded from any member of its stationary local fan: the member starts in
the auxiliary source and visits the edge gadget at its endpoint. -/
theorem edgeRequest_mem_familyEdges
    {L : PopularAuxiliary.Input Gamma I} {κ : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda κ}
    (S : Popular.PopularSeparator U) (e : edgeRequests L S.cut) :
    e.1 ∈ L.familyEdges := by
  let r : Request L S.cut := .inr e
  obtain ⟨a, ha⟩ := (requestFan_stationary S r).nonempty
  obtain ⟨p, hp, _hindex⟩ := ha
  have hfinish : p.finish = requestAuxVertex r :=
    Set.mem_singleton_iff.1 ((requestFan S r).ends_in_join hp)
  change p.finish =
    PopularAuxiliary.Input.LambdaVertex.edge e.1.1 e.1.2 at hfinish
  apply edgeNode_mem_familyEdges_of_start_in_source L p
    ((requestFan S r).starts_in_source hp)
  exact hfinish ▸ p.finish_mem_support

/-- Applying Theorem 8.4 to source-indexed auxiliary chronology supplies
all bridge data without an additional assumption. -/
def separatorOfSourceIndexed
    {L : PopularAuxiliary.Input Gamma I} {κ : Cardinal.{u}}
    (U : Popular.KappaUnbalanced L.lambda κ)
    (hU : U.toKappaIndexed.SourceIndexed) :
    Popular.PopularSeparator U.toKappaIndexed :=
  Popular.theorem8_4_of_sourceIndexed U hU

end PopularGroundingBridge
end Erdos599
