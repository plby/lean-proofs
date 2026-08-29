/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GlobalAdvance931

/-!
# Source roots at a reference/front splice

When a new front is source-star compatible with the reference warp, every
reference contact is the front's initial vertex.  If that vertex is already
in the incoming blueprint, the blueprint source-cover alternative rules out
losing the reference root: the root must be an actual blueprint initial and
therefore remains initial after the 9.30 cut.

This is the source-cover repair used by the canonical old-reference interval
row.  It is phrased only with the literal star compatibility and cut data, so
it is independent of the obsolete aggregate stage interface.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace SourceFrontAbsorption

/-- An initial of a concrete blueprint has no incoming edge in its edge
union.  This focused copy keeps the cut argument independent of the legacy
aggregate stage module. -/
theorem no_incoming_of_mem_initialSet
    (F : LinkageBlueprint Gamma Y kappa) {x : V}
    (hx : x ∈ F.initialSet) : ¬ ∃ y, (y, x) ∈ F.edgeSet := by
  rintro ⟨y, hyx⟩
  obtain ⟨p, hpF, hpinitial⟩ := hx
  simp only [edgeSet, Set.mem_iUnion] at hyx
  obtain ⟨q, hqF, hyxq⟩ := hyx
  have hxp : x ∈ p.support := hpinitial.symm ▸ p.initial_mem_support
  have hxq : x ∈ q.support :=
    (q.edgeSet_subset_support_prod hyxq).2
  have hpq : p = q :=
    F.path_eq_of_mem_support hpF hqF hxp hxq
  subst q
  rcases p with p | r
  · have hpstart : p.start = x := by
      simpa [DirectedPath.Path.initial] using hpinitial
    exact FinitePath.no_incoming_edge_at_start p y (hpstart ▸ hyxq)
  · obtain ⟨n, hn⟩ := hyxq
    have hzero : n + 1 = 0 := by
      apply r.injective
      calc
        r (n + 1) = x := (congrArg Prod.snd hn).symm
        _ = r.initial := hpinitial.symm
        _ = r 0 := rfl
    omega

/-- The initial set of a concrete blueprint is its set of carrier vertices
with no incoming edge. -/
theorem initialSet_eq_no_incoming
    (F : LinkageBlueprint Gamma Y kappa) :
    F.initialSet =
      {x | x ∈ F.vertexSet ∧ ¬ ∃ y, (y, x) ∈ F.edgeSet} := by
  ext x
  constructor
  · intro hx
    have hx' := hx
    obtain ⟨p, hpF, hpinitial⟩ := hx
    exact ⟨⟨p, hpF, hpinitial.symm ▸ p.initial_mem_support⟩,
      no_incoming_of_mem_initialSet F hx'⟩
  · rintro ⟨hxcarrier, hnoin⟩
    obtain ⟨p, hpF, hxp⟩ := hxcarrier
    refine ⟨p, hpF, ?_⟩
    by_contra hpinitial
    have hne : x ≠ p.initial := by
      intro h
      exact hpinitial h.symm
    rcases p with p | r
    · obtain ⟨y, hy⟩ :=
        FinitePath.exists_incoming_edge_of_mem_support_of_ne_start p hxp hne
      exact hnoin ⟨y, Set.mem_iUnion.2 ⟨Sum.inl p,
        Set.mem_iUnion.2 ⟨hpF, hy⟩⟩⟩
    · obtain ⟨n, hn⟩ := hxp
      have hnpos : 0 < n := by
        by_contra hnzero
        have : n = 0 := Nat.eq_zero_of_not_pos hnzero
        exact hne (by simpa [DirectedPath.Path.initial, Ray.initial, this]
          using hn.symm)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
      exact hnoin ⟨r m, Set.mem_iUnion.2 ⟨Sum.inr r,
        Set.mem_iUnion.2 ⟨hpF, ⟨m, by
          exact Prod.ext rfl hn.symm⟩⟩⟩⟩

theorem cut_vertexSet_eq
    {W cut : LinkageBlueprint Gamma Y kappa} {u : V}
    (hcut : W.IsCutAt cut u) : cut.vertexSet = W.vertexSet := by
  rcases hcut with ⟨_, rfl⟩ | ⟨v, hv⟩
  · rfl
  · exact hv.vertices_eq

theorem cut_edgeSet_subset
    {W cut : LinkageBlueprint Gamma Y kappa} {u : V}
    (hcut : W.IsCutAt cut u) : cut.edgeSet ⊆ W.edgeSet := by
  rcases hcut with ⟨_, rfl⟩ | ⟨v, hv⟩
  · exact Set.Subset.rfl
  · rw [hv.edges_eq]
    exact Set.sdiff_subset

/-- Deleting the optional outgoing imaginary edge cannot destroy an old
initial vertex. -/
theorem cut_initialSet_mono
    {W cut : LinkageBlueprint Gamma Y kappa} {u : V}
    (hcut : W.IsCutAt cut u) : W.initialSet ⊆ cut.initialSet := by
  rw [initialSet_eq_no_incoming W, initialSet_eq_no_incoming cut]
  rintro x ⟨hxW, hxin⟩
  refine ⟨?_, ?_⟩
  · rw [cut_vertexSet_eq hcut]
    exact hxW
  · rintro ⟨y, hyx⟩
    exact hxin ⟨y, cut_edgeSet_subset hcut hyx⟩

/-- A source-starting reference member which meets a compatible front must
retain its root after the cut, provided the common splice vertex belongs to
the incoming blueprint. -/
theorem root_mem_cutInitial_of_starCompatible
    {W cut : LinkageBlueprint Gamma Y kappa}
    {u : V} {T Z persistent : Set V}
    {I : Set Gamma.DPath} {front : FinitePath Gamma.graph}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hY : Gamma.IsWarp Y)
    (hcut : W.IsCutAt cut u)
    (huW : u ∈ W.vertexSet)
    (hcompat : Gamma.StarCompatible Y I)
    (hfront : (Sum.inl front : Gamma.DPath) ∈ I)
    (hstart : front.start = u)
    {p : Gamma.DPath} (hpY : p ∈ Y)
    (hpSource : p.initial ∈ Gamma.source)
    (hpFront : (p.support ∩ front.support).Nonempty) :
    p.initial ∈ cut.initialSet := by
  rcases hW.covers_source hpSource with hpInitial | hpRetained
  · exact cut_initialSet_mono hcut hpInitial
  · obtain ⟨q, hqRetained, hqInitial⟩ := hpRetained
    have hqp : q = p := by
      apply DWeb.IsWarp.eq_of_mem_support hY hqRetained.1.1 hpY
      · exact q.initial_mem_support
      · rw [hqInitial]
        exact p.initial_mem_support
    subst q
    obtain ⟨x, hxp, hxFront⟩ := hpFront
    have hcontact := hcompat p hpY (Sum.inl front) hfront x hxp hxFront
    have hfrontInitial : front.start = x := hcontact.2
    have hxu : x = u := hfrontInitial.symm.trans hstart
    apply False.elim
    apply hqRetained.2
    refine ⟨hpY, ⟨u, ?_, huW⟩⟩
    exact hxu ▸ hxp

/-- Family form used directly by the canonical interval front. -/
theorem all_roots_mem_cutInitial_of_starCompatible
    {W cut : LinkageBlueprint Gamma Y kappa}
    {u : V} {T Z persistent : Set V}
    {I : Set Gamma.DPath} {front : FinitePath Gamma.graph}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hY : Gamma.IsWarp Y)
    (hcut : W.IsCutAt cut u)
    (huW : u ∈ W.vertexSet)
    (hcompat : Gamma.StarCompatible Y I)
    (hfront : (Sum.inl front : Gamma.DPath) ∈ I)
    (hstart : front.start = u) :
    ∀ p ∈ Y, p.initial ∈ Gamma.source →
      (p.support ∩ front.support).Nonempty →
        p.initial ∈ cut.initialSet := by
  intro p hpY hpSource hpFront
  exact root_mem_cutInitial_of_starCompatible hW hY hcut huW hcompat
    hfront hstart hpY hpSource hpFront

#print axioms cut_initialSet_mono
#print axioms root_mem_cutInitial_of_starCompatible
#print axioms all_roots_mem_cutInitial_of_starCompatible

end SourceFrontAbsorption
end Erdos599.Blueprint.LinkageBlueprint
