/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeImaginaryClassification

/-!
# Native nondegenerate occurrences link into the reference terminal set

An infinite occurrence, or a finite nondegenerate occurrence, adds an
initial to a finite-character reference warp. Its switched source component
is a genuine finite path ending at a reference terminal. Its support is
confined to the occurrence and the reference owners meeting it. This is the
native linking step; the reference finite-character assumption is explicit.
-/

noncomputable section

namespace Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

open Set Cardinal Order DirectedPath Alternating Blueprint
open ColouredSafeAmbientOccurrence

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath} {s t : V}

def referenceClosure (A : CurrentSafeOccurrence W Y s) : Set V :=
  A.vertexSet ∪ meetingVertices Gamma Y A.vertexSet

theorem forwardEdges_subset_vertexSet_prod (A : CurrentSafeOccurrence W Y s) :
    A.forwardEdges ⊆ A.vertexSet ×ˢ A.vertexSet := by
  intro e he
  cases A with
  | infinite Q => exact Q.forwardEdges_endpoints_mem_vertexSet he
  | finite t Q => exact Q.forwardEdges_endpoints_mem_vertexSet he

theorem referenceClosure_forward_closed (A : CurrentSafeOccurrence W Y s)
    (hY : Gamma.IsWarp Y) {x y : V}
    (hx : x ∈ A.referenceClosure) (hxy : (x, y) ∈ A.switchedEdges) :
    y ∈ A.referenceClosure := by
  rcases hxy with hreference | hforward
  · have heY : (x, y) ∈ Alternating.familyEdges Y := hreference.1
    simp only [Alternating.familyEdges, Set.mem_iUnion] at heY
    obtain ⟨p, hp, hep⟩ := heY
    have hends := p.edgeSet_subset_support_prod hep
    have hmeet : (p.support ∩ A.vertexSet).Nonempty := by
      rcases hx with hxA | hxOwner
      · exact ⟨x, hends.1, hxA⟩
      · obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxOwner
        have hpq : p = q.1 :=
          DWeb.IsWarp.eq_of_mem_support hY hp q.2.1 hends.1 hxq
        simpa only [hpq] using q.2.2
    exact Or.inr (support_subset_meetingVertices Gamma Y A.vertexSet hp hmeet hends.2)
  · exact Or.inl (A.forwardEdges_subset_vertexSet_prod hforward).2

theorem finitePath_support_subset_referenceClosure_of_start_mem
    (A : CurrentSafeOccurrence W Y s) (hY : Gamma.IsWarp Y)
    (p : FinitePath Gamma.graph) (hstart : p.start ∈ A.referenceClosure)
    (hedges : p.edgeSet ⊆ A.switchedEdges) :
    p.support ⊆ A.referenceClosure := by
  have walk_closed : ∀ {x y : V} (w : Walk Gamma.graph x y),
      x ∈ A.referenceClosure → w.edgeSet ⊆ A.switchedEdges →
      ∀ z ∈ w.support, z ∈ A.referenceClosure := by
    intro x y w
    induction w with
    | @nil a =>
        intro hx _ z hz
        have hzx : z = a := by simpa only [Walk.support_nil, List.mem_singleton] using hz
        exact hzx ▸ hx
    | @cons x y z h w ih =>
        intro hx he v hv
        simp only [Walk.support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hx
        · apply ih (A.referenceClosure_forward_closed hY hx (he (by simp)))
            (fun e hew ↦ he (by simp [hew])) v hv
  apply walk_closed p.walk
  · exact hstart
  · exact hedges

theorem finitePath_support_subset_referenceClosure
    (A : CurrentSafeOccurrence W Y s) (hY : Gamma.IsWarp Y)
    (p : FinitePath Gamma.graph) (hstart : p.start = s)
    (hedges : p.edgeSet ⊆ A.switchedEdges) :
    p.support ⊆ A.referenceClosure :=
  A.finitePath_support_subset_referenceClosure_of_start_mem hY p
    (Or.inl (hstart.symm ▸ A.source_mem_vertexSet)) hedges

theorem hasFiniteSwitchedPathTo_self (A : CurrentSafeOccurrence W Y s) :
    A.HasFiniteSwitchedPathTo s := by
  refine ⟨⟨s, s, .nil, by simp [Walk.IsPath]⟩, rfl, rfl, ?_⟩
  simp [FinitePath.edgeSet, Walk.edgeSet]

/-- Closing the forbidden set under reference owners makes avoidance
survive passage from an occurrence to any switched source path. -/
theorem referenceClosure_inter_subset_of_avoids_closed_forbidden
    (A : CurrentSafeOccurrence W Y s)
    {X ends : Set V}
    (hends : Disjoint ends (Gamma.vertexSet Y))
    (havoid : A.vertexSet ∩ (X ∪ meetingVertices Gamma Y X) ⊆ ends) :
    A.referenceClosure ∩ X ⊆ ends := by
  rintro x ⟨hxA | hxOwner, hxX⟩
  · exact havoid ⟨hxA, Or.inl hxX⟩
  · obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hxOwner
    obtain ⟨y, hyp, hyA⟩ := p.2.2
    have hyClosed : y ∈ meetingVertices Gamma Y X :=
      support_subset_meetingVertices Gamma Y X p.2.1 ⟨x, hxp, hxX⟩ hyp
    have hyEnds := havoid ⟨hyA, Or.inr hyClosed⟩
    exact False.elim (Set.disjoint_left.mp hends hyEnds ⟨p.1, p.2.1, hyp⟩)

end Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace Erdos599.ColouredSafeAmbientOccurrence

open Set DirectedPath Alternating
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {s t : V}

private theorem exists_source_member
    {U : Set Gamma.DPath} (hfinite : Gamma.HasFiniteCharacter U)
    (hs : s ∈ Gamma.initialSet U) :
    ∃ p : FinitePath Gamma.graph, (Sum.inl p : Gamma.DPath) ∈ U ∧ p.start = s := by
  obtain ⟨q, hq, hqs⟩ := hs
  obtain ⟨p, hp⟩ := hfinite hq
  subst q
  exact ⟨p, hq, hqs⟩

/-- The finite nondegenerate branch ends at an old reference terminal,
because its source component cannot end at the new terminal. -/
theorem Valid.exists_referenceTerminal_path_of_nondegenerate
    {A : Occurrence Y s} (hA : Valid A)
    (hY : Gamma.IsWarp Y) (hfinite : Gamma.HasFiniteCharacter Y)
    (hend : A.terminal? = some t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    (hnondeg : ¬A.HasFiniteSwitchedPathTo t) :
    ∃ p : FinitePath Gamma.graph, p.start = s ∧
      p.finish ∈ Gamma.terminalFrontier Y ∧
      p.edgeSet ⊆ A.switchedEdges ∧ p.support ⊆ A.referenceClosure := by
  have hne : s ≠ t := by
    rintro rfl
    exact hnondeg A.hasFiniteSwitchedPathTo_self
  obtain ⟨U, _hU, hUfinite, hUE, _hUI, hUinitial, hUterminal⟩ :=
    hA.exists_finiteWarp_of_terminal hY hfinite hend hne hs ht
  obtain ⟨p, hp, hps⟩ := exists_source_member hUfinite
    (s := s) (hUinitial.symm ▸ (Or.inr (Set.mem_singleton s)))
  have hpe : p.edgeSet ⊆ A.switchedEdges := by
    intro e he
    rw [← hUE]
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨Sum.inl p, hp, he⟩
  have hpt : p.finish ∈ Gamma.terminalFrontier Y := by
    have hterm : p.finish ∈ Gamma.terminalFrontier U := ⟨Sum.inl p, hp, rfl⟩
    rw [hUterminal] at hterm
    rcases hterm with hterm | hnew
    · exact hterm
    · exact False.elim (hnondeg ⟨p, hps, Set.mem_singleton_iff.mp hnew, hpe⟩)
  exact ⟨p, hps, hpt, hpe, A.finitePath_support_subset_referenceClosure hY p hps hpe⟩

/-- Even an infinite native occurrence switches to a finite source path
when both covering warps have finite character. -/
theorem Valid.exists_referenceTerminal_path_of_infinite
    {A : Occurrence Y s} (hA : Valid A)
    (hY : Gamma.IsWarp Y) (hfinite : Gamma.HasFiniteCharacter Y)
    (hend : A.terminal? = none) (hs : s ∉ Gamma.vertexSet Y) :
    ∃ p : FinitePath Gamma.graph, p.start = s ∧
      p.finish ∈ Gamma.terminalFrontier Y ∧
      p.edgeSet ⊆ A.switchedEdges ∧ p.support ⊆ A.referenceClosure := by
  obtain ⟨U, _hU, hUfinite, hUE, _hUI, hUinitial, hUterminal⟩ :=
    hA.exists_finiteWarp_of_infinite hY hfinite hend hs
  obtain ⟨p, hp, hps⟩ := exists_source_member hUfinite
    (s := s) (hUinitial.symm ▸ (Or.inr (Set.mem_singleton s)))
  have hpe : p.edgeSet ⊆ A.switchedEdges := by
    intro e he
    rw [← hUE]
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨Sum.inl p, hp, he⟩
  have hpt : p.finish ∈ Gamma.terminalFrontier Y := by
    rw [← hUterminal]
    exact ⟨Sum.inl p, hp, rfl⟩
  exact ⟨p, hps, hpt, hpe, A.finitePath_support_subset_referenceClosure hY p hps hpe⟩

#print axioms CurrentSafeOccurrence.finitePath_support_subset_referenceClosure
#print axioms CurrentSafeOccurrence.referenceClosure_inter_subset_of_avoids_closed_forbidden
#print axioms Valid.exists_referenceTerminal_path_of_nondegenerate
#print axioms Valid.exists_referenceTerminal_path_of_infinite

end Erdos599.ColouredSafeAmbientOccurrence

namespace Erdos599.Blueprint.ColouredSafeHammock

open Set Cardinal Order DirectedPath
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {s : V}

/-- Choose one actual large-hammock member avoiding a small forbidden set
after all reference owners meeting that set have been reserved. The whole
switched source component, not just the occurrence, then avoids the set
apart from its prescribed exposed endpoints. -/
theorem HasCard.exists_goodRoute_avoiding_referenceClosure
    {e : Option V} {extra : Occurrence Y s → Prop} {rho : Cardinal.{u}}
    (h : HasCard Y s e extra (succ rho))
    (hY : Gamma.IsWarp Y) (hrho : aleph0 ≤ rho)
    {X : Set V} (hX : #X ≤ rho) :
    ∃ A : Occurrence Y s, A ∈ goodRoutes Y s e extra ∧
      A.referenceClosure ∩ X ⊆ endpoints s e := by
  let reserve := X ∪ meetingVertices Gamma Y X
  have hreserve : #reserve ≤ rho :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hrho hX
      (mk_meetingVertices_le Gamma Y X hY hrho hX))
  obtain ⟨H, hH, hcard⟩ := h
  obtain ⟨A, _hAH, hgood, hdisj⟩ := exists_mem_avoiding hH hcard hreserve
  refine ⟨A, hgood, ?_⟩
  apply A.referenceClosure_inter_subset_of_avoids_closed_forbidden
  · apply Set.disjoint_left.mpr
    intro x hx hxY
    rcases hx with hxs | hxt
    · exact hgood.2.2.1 (Set.mem_singleton_iff.mp hxs ▸ hxY)
    · exact hgood.2.2.2.1 x hxt hxY
  · rintro x ⟨hxA, hxReserve⟩
    by_contra hxNotEnd
    exact Set.disjoint_left.mp hdisj ⟨hxA, hxNotEnd⟩ hxReserve

/-- A large native nondegenerate or infinite hammock produces a genuine
finite source-to-reference-terminal path avoiding any prescribed small set
away from its exposed ends. The chosen occurrence still satisfies its
original filter. -/
theorem HasCard.exists_referenceTerminal_path_avoiding
    {e : Option V} {extra : Occurrence Y s → Prop} {rho : Cardinal.{u}}
    (h : HasCard Y s e extra (succ rho))
    (hY : Gamma.IsWarp Y) (hfinite : Gamma.HasFiniteCharacter Y)
    (hrho : aleph0 ≤ rho)
    (hnondeg : ∀ A, extra A → ∀ t, e = some t → ¬A.HasFiniteSwitchedPathTo t)
    {X : Set V} (hX : #X ≤ rho) :
    ∃ (A : Occurrence Y s) (p : FinitePath Gamma.graph),
      A ∈ goodRoutes Y s e extra ∧ p.start = s ∧
      p.finish ∈ Gamma.terminalFrontier Y ∧
      p.edgeSet ⊆ A.switchedEdges ∧ p.support ∩ X ⊆ endpoints s e := by
  obtain ⟨A, hA, havoid⟩ := h.exists_goodRoute_avoiding_referenceClosure hY hrho hX
  have hpath : ∃ p : FinitePath Gamma.graph, p.start = s ∧
      p.finish ∈ Gamma.terminalFrontier Y ∧
      p.edgeSet ⊆ A.switchedEdges ∧ p.support ⊆ A.referenceClosure := by
    cases he : e with
    | none =>
        exact hA.1.exists_referenceTerminal_path_of_infinite hY hfinite
          (hA.2.1.trans he) hA.2.2.1
    | some t =>
        exact hA.1.exists_referenceTerminal_path_of_nondegenerate hY hfinite
          (hA.2.1.trans he) hA.2.2.1 (hA.2.2.2.1 t he)
          (hnondeg A hA.2.2.2.2 t he)
  obtain ⟨p, hps, hpt, hpe, hpSupport⟩ := hpath
  exact ⟨A, p, hA, hps, hpt, hpe,
    fun _ hx ↦ havoid ⟨hpSupport hx.1, hx.2⟩⟩

#print axioms HasCard.exists_goodRoute_avoiding_referenceClosure
#print axioms HasCard.exists_referenceTerminal_path_avoiding

end Erdos599.Blueprint.ColouredSafeHammock
