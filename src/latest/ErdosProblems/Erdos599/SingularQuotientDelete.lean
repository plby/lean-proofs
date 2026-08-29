/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularContinuation

/-!
# Quotient-then-deletion transport for singular continuation

These lemmas isolate the safe order of operations for a singular successor:
first quotient by the pending boundary, then delete frozen boundary sources,
and finally restore that deletion before source-starring the pending warp.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularExtension

universe u

variable {V : Type u}

/-- The only frozen vertices which must be explicitly deleted after
quotienting are those on the commitment boundary.  Frozen vertices strictly
behind that boundary are removed by the quotient itself. -/
def frozenBoundary (G : DWeb V) (F : Set G.DPath) (C : Set V) : Set V :=
  G.vertexSet F ∩ C

/-- The part of a frozen family which is not already removed by quotienting
by `C`.  This is the canonical deletion set for a sound singular successor.

Unlike `frozenBoundary`, this definition makes no roof-containment
assumption on `F`.  That distinction matters when a completed path starts in
the stop-over: its internal vertices need not lie in `strictRoof C`. -/
def frozenUnsafe (G : DWeb V) (F : Set G.DPath) (C : Set V) : Set V :=
  G.vertexSet F \ G.strictRoof C

/-- Deleting `frozenUnsafe` and quotienting by `C` removes every frozen
vertex: a frozen vertex is either explicitly deleted or already belongs to
the strict roof discarded by the quotient. -/
theorem vertexSet_subset_frozenUnsafe_union_strictRoof
    (G : DWeb V) (F : Set G.DPath) (C : Set V) :
    G.vertexSet F ⊆ frozenUnsafe G F C ∪ G.strictRoof C := by
  intro x hxF
  by_cases hxStrict : x ∈ G.strictRoof C
  · exact Or.inr hxStrict
  · exact Or.inl ⟨hxF, hxStrict⟩

/-- Under the additional roof containment used by the older boundary-only
transport, the canonical unsafe set is contained in the boundary and hence
in the quotient source.  Without that containment the conclusion is false;
the unsafe set may contain internal vertices of a completed path. -/
theorem frozenUnsafe_subset_frozenBoundary
    (G : DWeb V) {F : Set G.DPath} {C : Set V}
    (htrim : IsTrimmedSeparator G C)
    (hroof : G.vertexSet F ⊆ G.roof C) :
    frozenUnsafe G F C ⊆ frozenBoundary G F C := by
  rintro x ⟨hxF, hxNotStrict⟩
  refine ⟨hxF, ?_⟩
  have hxRoof : x ∈ G.roof C := hroof hxF
  by_contra hxC
  apply hxNotStrict
  refine ⟨hxRoof, ?_⟩
  intro hxEssential
  exact hxC (htrim ▸ hxEssential)

theorem frozenBoundary_subset_quotientSource
    (G : DWeb V) {F : Set G.DPath} {C : Set V}
    (hCsource : C ⊆ (G.quotient C).source) :
    frozenBoundary G F C ⊆ (G.quotient C).source := by
  intro x hx
  exact hCsource hx.2

/-- Roof containment of the frozen family gives exactly the decomposition
required by safe quotient-delete transport. -/
theorem vertexSet_subset_frozenBoundary_union_strictRoof
    (G : DWeb V) {F : Set G.DPath} {C : Set V}
    (htrim : IsTrimmedSeparator G C)
    (hroof : G.vertexSet F ⊆ G.roof C) :
    G.vertexSet F ⊆ frozenBoundary G F C ∪ G.strictRoof C := by
  intro x hxF
  by_cases hxC : x ∈ C
  · exact Or.inl ⟨hxF, hxC⟩
  · refine Or.inr ⟨hroof hxF, ?_⟩
    intro hxEssential
    exact hxC (htrim ▸ hxEssential)

/-- A pending frontier disjoint from the frozen warp survives deletion of
the frozen boundary and remains a source of the quotient-delete web. -/
theorem terminalFrontier_subset_quotientDelete_source
    (G : DWeb V) {F W : Set G.DPath} {C : Set V}
    (hCsource : C ⊆ (G.quotient C).source)
    (hfrontier : G.terminalFrontier W ⊆ C)
    (hFW : Disjoint (G.vertexSet F) (G.vertexSet W)) :
    G.terminalFrontier W ⊆
      ((G.quotient C).delete (frozenBoundary G F C)).source := by
  intro x hxFrontier
  refine ⟨hCsource (hfrontier hxFrontier), ?_⟩
  rintro ⟨hxF, _hxC⟩
  obtain ⟨p, hpW, hpx⟩ := hxFrontier
  exact Set.disjoint_left.1 hFW hxF
    ⟨p, hpW, G.terminal_mem_support hpx⟩

/-- Direct quotient-then-deletion transport avoids the old strict roof,
provided all restored paths start in the trimmed commitment set. -/
theorem disjoint_liftQuotientDeleteFamily_strictRoof
    (G : DWeb V) {C Q : Set V}
    (htrim : IsTrimmedSeparator G C)
    {U : Set ((G.quotient C).delete Q).DPath}
    (hUstart : ((G.quotient C).delete Q).initialSet U ⊆ C) :
    Disjoint
      (G.vertexSet
        (G.liftQuotientFamily C
          ((G.quotient C).liftDeleteFamily Q U)))
      (G.strictRoof C) := by
  apply Set.disjoint_left.2
  intro x hxU hxStrict
  obtain ⟨p, hpU', hxp⟩ := hxU
  obtain ⟨q, hqU', rfl⟩ := hpU'
  obtain ⟨q₀, hq₀U, rfl⟩ := hqU'
  let q' : (G.quotient C).DPath :=
    (G.quotient C).liftDeletePath Q q₀
  have hxq' : x ∈ q'.support := by
    simpa [q'] using hxp
  rcases G.quotientPath_support_initial_or_avoids C q' hxq' with
    hxInitial | hxAvoid
  · have hxC : x ∈ C := by
      rw [hxInitial]
      have hq₀C : q₀.initial ∈ C := hUstart ⟨q₀, hq₀U, rfl⟩
      simpa [q'] using hq₀C
    have hxEssential : x ∈ G.essential C := htrim.symm ▸ hxC
    exact Set.disjoint_left.1 (G.disjoint_strictRoof_essential C)
      hxStrict hxEssential
  · exact hxAvoid.1 hxStrict

/-- Quotient first and delete frozen boundary sources second.  Once `Q` is
known to lie in `(G / C).source`, a lower-cardinal half-way family can be
chosen in `(G / C) - Q`.  Restoring that deletion produces all geometric
premises required by the frozen/pending continuation. -/
theorem exists_frozenPendingContinuation_of_quotientDeleteFamily
    (G : DWeb V) {F W : Set G.DPath} {C Q : Set V}
    (hF : G.IsWarp F) (hW : G.IsWarp W)
    (hFfinite : G.HasFiniteCharacter F)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : SingularContinuation.TerminalCleanAt G W C)
    {U : Set ((G.quotient C).delete Q).DPath}
    (hU : ((G.quotient C).delete Q).IsWarp U)
    (hUfinite : ((G.quotient C).delete Q).HasFiniteCharacter U)
    (hUsource : ((G.quotient C).delete Q).initialSet U ⊆
      ((G.quotient C).delete Q).source)
    (hUstart : ((G.quotient C).delete Q).initialSet U ⊆ C)
    (hcover : G.terminalFrontier W ⊆
      ((G.quotient C).delete Q).initialSet U)
    (hFW : Disjoint (G.vertexSet F) (G.vertexSet W))
    (hFsafe : G.vertexSet F ⊆ Q ∪ G.strictRoof C) :
    ∃ W' : Set G.DPath,
      G.IsWarp W' ∧ G.HasFiniteCharacter W' ∧
      G.ForwardExtension (F ∪ W) W' ∧
      G.initialSet W' = G.initialSet (F ∪ W) ∧
      G.terminalFrontier W' ⊆
        G.terminalFrontier F ∪
          (G.quotient C).terminalFrontier
            ((G.quotient C).liftDeleteFamily Q U) := by
  let U' : Set (G.quotient C).DPath :=
    (G.quotient C).liftDeleteFamily Q U
  have hU' : (G.quotient C).IsWarp U' := hU.liftDeleteFamily
  have hU'finite : (G.quotient C).HasFiniteCharacter U' := by
    exact (G.quotient C).fd_hasFiniteCharacter_liftDeleteFamily hUfinite
  have hU'initial : (G.quotient C).initialSet U' =
      ((G.quotient C).delete Q).initialSet U := by
    exact (G.quotient C).initialSet_liftDeleteFamily Q U
  have hU'start : (G.quotient C).initialSet U' ⊆ C := by
    rw [hU'initial]
    exact hUstart
  have hU'cover : G.terminalFrontier W ⊆
      (G.quotient C).initialSet U' := by
    rw [hU'initial]
    exact hcover
  have hsafeQ : Disjoint
      ((G.quotient C).vertexSet U') Q := by
    exact (G.quotient C).vertexSet_liftDeleteFamily_disjoint hUsource
  have hsafe : Disjoint
      (G.vertexSet (G.liftQuotientFamily C U')) Q := by
    apply Set.disjoint_left.2
    intro x hx hxQ
    obtain ⟨p, ⟨q, hqU', rfl⟩, hxp⟩ := hx
    exact Set.disjoint_left.1 hsafeQ
      ⟨q, hqU', by simpa using hxp⟩ hxQ
  have hsafeStrict : Disjoint
      (G.vertexSet (G.liftQuotientFamily C U'))
      (G.strictRoof C) := by
    exact disjoint_liftQuotientDeleteFamily_strictRoof G htrim hUstart
  have hFU : Disjoint (G.vertexSet F)
      (G.vertexSet (SingularContinuation.liftedQuotientFamily G C U')) := by
    apply Set.disjoint_left.2
    intro x hxF hxU'
    rcases hFsafe hxF with hxQ | hxStrict
    · exact Set.disjoint_left.1 hsafe hxU' hxQ
    · exact Set.disjoint_left.1 hsafeStrict hxU' hxStrict
  exact SingularContinuation.exists_frozenPendingContinuation_of_componentwise_disjoint
    G hF hW hFfinite hWfinite hroof htrim hclean hU' hU'finite
      hU'start hU'cover hFW hFU

/-- Canonical strict-roof-safe specialization.  No separate assertion about
the location of frozen vertices is required: the deletion set is precisely
the part of the frozen support which survives the quotient.

This theorem deliberately does not assert that the quotient-delete web is
unhindered.  Establishing that fact is the graph-theoretic selection
obligation required before a lower-cardinal half-way clause can furnish
`U`; it does not follow from separating-stop-over data alone. -/
theorem exists_frozenPendingContinuation_of_frozenUnsafe
    (G : DWeb V) {F W : Set G.DPath} {C : Set V}
    (hF : G.IsWarp F) (hW : G.IsWarp W)
    (hFfinite : G.HasFiniteCharacter F)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : SingularContinuation.TerminalCleanAt G W C)
    {U : Set
      ((G.quotient C).delete (frozenUnsafe G F C)).DPath}
    (hU : ((G.quotient C).delete (frozenUnsafe G F C)).IsWarp U)
    (hUfinite :
      ((G.quotient C).delete (frozenUnsafe G F C)).HasFiniteCharacter U)
    (hUsource :
      ((G.quotient C).delete (frozenUnsafe G F C)).initialSet U ⊆
        ((G.quotient C).delete (frozenUnsafe G F C)).source)
    (hUstart :
      ((G.quotient C).delete (frozenUnsafe G F C)).initialSet U ⊆ C)
    (hcover : G.terminalFrontier W ⊆
      ((G.quotient C).delete (frozenUnsafe G F C)).initialSet U)
    (hFW : Disjoint (G.vertexSet F) (G.vertexSet W)) :
    ∃ W' : Set G.DPath,
      G.IsWarp W' ∧ G.HasFiniteCharacter W' ∧
      G.ForwardExtension (F ∪ W) W' ∧
      G.initialSet W' = G.initialSet (F ∪ W) ∧
      G.terminalFrontier W' ⊆
        G.terminalFrontier F ∪
          (G.quotient C).terminalFrontier
            ((G.quotient C).liftDeleteFamily
              (frozenUnsafe G F C) U) := by
  exact exists_frozenPendingContinuation_of_quotientDeleteFamily
    G hF hW hFfinite hWfinite hroof htrim hclean hU hUfinite
      hUsource hUstart hcover hFW
      (vertexSet_subset_frozenUnsafe_union_strictRoof G F C)

end SingularExtension
end CardinalInduction
end Erdos599
