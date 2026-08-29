/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingRelationalIntervalStep

/-!
# Reference-contact preservation in a forward/backward step

Only the first and last vertices of the new forward fragment may be new
reference contacts. Its other reference contacts lie in interiors of the
old removed intervals. An old removed edge leaves the first vertex, and
the new backward interval supplies an edge entering the last vertex.
These local facts construct all new incidence-removal and endpoint-purity
certificates; no alternating-trace collision normal form is assumed.
-/

namespace Erdos599.Alternating.SwitchingCore.RelationalInterval

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

theorem new_forward_contacts_have_removed_incidence
    {Y : Set Gamma.DPath} {R N : Set (V × V)}
    (p : FinitePath Gamma.graph)
    (hstart : p.start ∈ Gamma.vertexSet Y → HasOutgoing R p.start)
    (hfinish : p.finish ∈ Gamma.vertexSet Y → HasIncoming N p.finish)
    (hcontact : p.support ∩ Gamma.vertexSet Y ⊆
      {p.start, p.finish} ∪ removedInterior R) :
    ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      (y ∈ Gamma.vertexSet Y → HasIncoming (R ∪ N) y) ∧
      (x ∈ Gamma.vertexSet Y → HasOutgoing (R ∪ N) x) := by
  intro x y hxy
  constructor
  · intro hyY
    have hy := hcontact ⟨(p.edgeSet_subset_support_prod hxy).2, hyY⟩
    rcases hy with hy | hy
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · exact (FinitePath.no_incoming_edge_at_start p x (hy ▸ hxy)).elim
      · obtain ⟨z, hz⟩ := hfinish (hy ▸ hyY)
        exact ⟨z, Or.inr (hy ▸ hz)⟩
    · obtain ⟨z, hz⟩ := hy.1
      exact ⟨z, Or.inl hz⟩
  · intro hxY
    have hx := hcontact ⟨(p.edgeSet_subset_support_prod hxy).1, hxY⟩
    rcases hx with hx | hx
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · obtain ⟨z, hz⟩ := hstart (hx ▸ hxY)
        exact ⟨z, Or.inl (hx ▸ hz)⟩
      · exact (FinitePath.no_outgoing_edge_at_finish p y (hx ▸ hxy)).elim
    · obtain ⟨z, hz⟩ := hx.2
      exact ⟨z, Or.inl hz⟩

/-- The first-contact geometry constructs the exact cross-incidence
condition for every new forward edge. -/
theorem new_forward_conflicting_edges_removed
    {Y : Set Gamma.DPath} {R N : Set (V × V)} (hY : Gamma.IsWarp Y)
    (hR : R ⊆ familyEdges Y) (hN : N ⊆ familyEdges Y)
    (p : FinitePath Gamma.graph)
    (hstart : p.start ∈ Gamma.vertexSet Y → HasOutgoing R p.start)
    (hfinish : p.finish ∈ Gamma.vertexSet Y → HasIncoming N p.finish)
    (hcontact : p.support ∩ Gamma.vertexSet Y ⊆
      {p.start, p.finish} ∪ removedInterior R) :
    (∀ {a b x : V}, (a, x) ∈ p.edgeSet →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R ∪ N) ∧
    (∀ {x a b : V}, (x, a) ∈ p.edgeSet →
      (x, b) ∈ familyEdges Y → (x, b) ∈ R ∪ N) := by
  have hsub : R ∪ N ⊆ familyEdges Y := Set.union_subset hR hN
  constructor
  · intro a b x hax hbx
    obtain ⟨z, hz⟩ :=
      (new_forward_contacts_have_removed_incidence p hstart hfinish hcontact hax).1
        (familyEdges_subset_vertexSet_prod Y hbx).2
    have hzb : z = b := (IsWarp.familyEdges_biUnique hY).1 (hsub hz) hbx
    exact hzb ▸ hz
  · intro x a b hxa hxb
    obtain ⟨z, hz⟩ :=
      (new_forward_contacts_have_removed_incidence p hstart hfinish hcontact hxa).2
        (familyEdges_subset_vertexSet_prod Y hxb).1
    have hzb : z = b := (IsWarp.familyEdges_biUnique hY).2 (hsub hz) hxb
    exact hzb ▸ hz

/-- The same contact geometry prevents the new inserted edges from
entering a reference initial or leaving a reference terminal. -/
theorem new_forward_endpoint_pure
    {Y : Set Gamma.DPath} {R N : Set (V × V)} (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (hR : R ⊆ familyEdges Y) (hN : N ⊆ familyEdges Y)
    (p : FinitePath Gamma.graph)
    (hstart : p.start ∈ Gamma.vertexSet Y → HasOutgoing R p.start)
    (hfinish : p.finish ∈ Gamma.vertexSet Y → HasIncoming N p.finish)
    (hcontact : p.support ∩ Gamma.vertexSet Y ⊆
      {p.start, p.finish} ∪ removedInterior R) :
    ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y := by
  intro x y hxy
  have hinc := new_forward_contacts_have_removed_incidence
    p hstart hfinish hcontact hxy
  have hsub : R ∪ N ⊆ familyEdges Y := Set.union_subset hR hN
  constructor
  · intro hy
    rw [initialSet_eq_vertexSet_diff_hasIncoming hY hYfin] at hy
    obtain ⟨z, hz⟩ := hinc.1 hy.1
    exact hy.2 ⟨z, hsub hz⟩
  · intro hx
    rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hY hYfin] at hx
    obtain ⟨z, hz⟩ := hinc.2 hx.1
    exact hx.2 ⟨z, hsub hz⟩

#print axioms new_forward_conflicting_edges_removed
#print axioms new_forward_endpoint_pure

end Erdos599.Alternating.SwitchingCore.RelationalInterval
