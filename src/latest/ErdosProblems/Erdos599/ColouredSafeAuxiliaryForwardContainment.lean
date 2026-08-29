/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeForwardStopping
import ErdosProblems.Erdos599.FiniteSafeSearchTerminalFidelity

/-!
# Bounding an actual auxiliary forward continuation

The carrier is the original finite saturation carrier, not a forward-closed
set postulated for the argument. Safe stopping and finite uncapping put the
whole original owner of an off-reference contact in that carrier. A wholly
internal reference fragment uses the separate internal-edge hypothesis.
-/

namespace Erdos599.Alternating.ColouredSafeAuxiliaryForwardContainment

open Set DirectedPath FiniteColouredOccurrenceWord ColouredSafeReverseReachability
open SwitchingCore SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y C : Set Gamma.DPath}

theorem safe_endpoint_owner_subset_saturation
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    {J : Set (ExposedInitial W Y)}
    (Q : FiniteColouredOccurrenceWord W Y) (hQ : Q.IsIntervalSafe)
    (hfirstJ : Q.vertex 0 ∈ Subtype.val '' J)
    (hlastW : Q.vertex (Fin.last Q.length) ∈ Gamma.vertexSet W)
    (hlastOff : Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y) :
    coveredPathSupport hW (Q.vertex (Fin.last Q.length)) ⊆
      finiteSaturationCarrier hW hY J := by
  obtain ⟨⟨s, hsW, hsY⟩, hsJ, hs⟩ := hfirstJ
  change s = Q.vertex 0 at hs
  subst s
  exact (safe_endpoint_owner_subset_safeSearchCarrier hW hY hWfin hYfin
    Q hQ hsW hsY hlastW hlastOff).trans
      (sourceSearchCarrier_subset_finiteSaturationCarrier hW hY hsJ)

theorem source_owner_subset_saturation
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    {J : Set (ExposedInitial W Y)} {x : V} (hx : x ∈ Subtype.val '' J) :
    coveredPathSupport hW x ⊆ finiteSaturationCarrier hW hY J := by
  obtain ⟨s, hsJ, rfl⟩ := hx
  exact safe_endpoint_owner_subset_saturation hW hY hWfin hYfin
    (emptyAt s.1) (emptyAt_isIntervalSafe s.1) ⟨s, hsJ, rfl⟩
    (initialSet_subset_vertexSet W s.2.1) s.2.2

theorem safeTerminal_owner_subset_saturation
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    {J : Set (ExposedInitial W Y)} {x : V} (hx : x ∈ safeTerminalUnion J) :
    coveredPathSupport hW x ⊆ finiteSaturationCarrier hW hY J := by
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hsJ, ht, Q, hQ, hfirst, hlast⟩ := Set.mem_iUnion.mp hs
  have hbound := safe_endpoint_owner_subset_saturation hW hY hWfin hYfin
    Q hQ ⟨s, hsJ, hfirst.symm⟩
    (hlast ▸ terminalFrontier_subset_vertexSet W ht.1) (hlast ▸ ht.2)
  simpa only [hlast] using hbound

theorem source_or_safeTerminal_mem_saturation
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    {J : Set (ExposedInitial W Y)} {x : V}
    (hx : x ∈ Subtype.val '' J ∪ safeTerminalUnion J) :
    x ∈ finiteSaturationCarrier hW hY J := by
  have of_owner (hxW : x ∈ Gamma.vertexSet W)
      (howner : coveredPathSupport hW x ⊆ finiteSaturationCarrier hW hY J) :
      x ∈ finiteSaturationCarrier hW hY J := by
    obtain ⟨p, hp, hxp⟩ := hxW
    rw [coveredPathSupport_eq_of_mem hW hp hxp] at howner
    exact howner hxp
  rcases hx with hxJ | hxN
  · apply of_owner _ (source_owner_subset_saturation hW hY hWfin hYfin hxJ)
    obtain ⟨s, _hsJ, rfl⟩ := hxJ
    exact initialSet_subset_vertexSet W s.2.1
  · apply of_owner _ (safeTerminal_owner_subset_saturation hW hY hWfin hYfin hxN)
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hxN
    obtain ⟨_hsJ, hxs⟩ := Set.mem_iUnion.mp hs
    exact terminalFrontier_subset_vertexSet W hxs.1.1

private theorem forward_support_subset_owner_at_point
    (hW : Gamma.IsWarp W) (p : FinitePath Gamma.graph)
    (hne : p.start ≠ p.finish) (hp : p.edgeSet ⊆ familyEdges W)
    {x : V} (hx : x ∈ p.support) : p.support ⊆ coveredPathSupport hW x := by
  obtain ⟨r, hr, hpr⟩ := finitePath_isFragmentOf_of_edgeSet_subset_familyEdges hW p hne hp
  rw [coveredPathSupport_eq_of_mem hW hr (hpr.1 hx)]
  exact hpr.1

/-- Every actual fresh forward fragment remains in the original saturation
carrier, provided its internal reference edges really are reference edges.
No finiteness of the ambient family carriers is assumed. -/
theorem forward_support_subset_saturation
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hYC : Gamma.IsWarp (Y ∪ C)) (hYCfin : Gamma.HasFiniteCharacter (Y ∪ C))
    (hdisjoint : Disjoint (Gamma.vertexSet Y) (Gamma.vertexSet C))
    {J : Set (ExposedInitial W Y)}
    (hCtails : ∀ {x y}, (x, y) ∈ familyEdges C → x ∈ Subtype.val '' J)
    (hCV : Gamma.vertexSet C ⊆ Subtype.val '' J ∪ safeTerminalUnion J)
    (Q : FiniteColouredOccurrenceWord W (Y ∪ C)) (hQ : Q.IsIntervalSafe)
    (hfirstJ : Q.vertex 0 ∈ Subtype.val '' J)
    (hfirstOff : Q.vertex 0 ∉ Gamma.vertexSet (Y ∪ C))
    (hQH : Q.vertexSet ⊆ finiteSaturationCarrier hW hY J)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish)
    (hjoin : Q.vertex (Fin.last Q.length) = p.start)
    (hp : p.edgeSet ⊆ familyEdges W) (hfresh : Disjoint p.edgeSet Q.forwardEdges)
    (hfinish : p.finish ∈ Gamma.vertexSet (Y ∪ C))
    (hstart : p.start ∈ Gamma.vertexSet (Y ∪ C) → HasOutgoing Q.backwardEdges p.start)
    (hcontact : p.support ∩ Gamma.vertexSet (Y ∪ C) ⊆
      {p.start, p.finish} ∪ removedInterior Q.backwardEdges)
    (hinternal : ∀ {a b}, (a, b) ∈ p.edgeSet → a ∈ Gamma.vertexSet Y →
      b ∈ Gamma.vertexSet Y → (a, b) ∈ familyEdges Y) :
    p.support ⊆ finiteSaturationCarrier hW hY J := by
  classical
  by_cases hx : ∃ x ∈ p.support, x ∉ Gamma.vertexSet Y
  · obtain ⟨x, hxp, hxY⟩ := hx
    apply (forward_support_subset_owner_at_point hW p hne hp hxp).trans
    by_cases hxC : x ∈ Gamma.vertexSet C
    · rcases hCV hxC with hxJ | hxN
      · exact source_owner_subset_saturation hW hY hWfin hYfin hxJ
      · exact safeTerminal_owner_subset_saturation hW hY hWfin hYfin hxN
    by_cases hxFirst : x = Q.vertex 0
    · exact source_owner_subset_saturation hW hY hWfin hYfin (hxFirst ▸ hfirstJ)
    have hxOff : x ∉ Gamma.vertexSet (Y ∪ C) := by
      rw [DWeb.vertexSet_union]
      exact fun h ↦ h.elim hxY hxC
    obtain ⟨P, hP, hPfirst, hPlast, _hPF⟩ :=
      ColouredSafeForwardStopping.exists_safeWord_to_offReference_forwardPoint
        hYC hYCfin Q hQ p hjoin hp hfresh hfinish hstart hcontact hxp hxOff
    have hdistinct : P.vertex 0 ≠ P.vertex (Fin.last P.length) := by
      intro he
      exact hxFirst (hPlast.symm.trans (he.symm.trans hPfirst))
    obtain ⟨s, hsJ, T, hT, hTfirst, hTlast, _hTF⟩ :=
      ColouredSafeFiniteAuxiliaryRemoval.exists_originalSafeWord hW hY hWfin hYfin
        hYC hdisjoint hCtails P hP (hPfirst ▸ hfirstJ)
        (hPfirst ▸ hfirstOff) (hPlast ▸ hxOff) hdistinct
    have hxW : x ∈ Gamma.vertexSet W := by
      obtain ⟨r, hr, hpr⟩ := finitePath_isFragmentOf_of_edgeSet_subset_familyEdges hW p hne hp
      exact ⟨r, hr, hpr.1 hxp⟩
    have hTfinish : T.vertex (Fin.last T.length) = x := hTlast.trans hPlast
    have hbound := safe_endpoint_owner_subset_saturation hW hY hWfin hYfin T hT
      (hTfirst ▸ hsJ) (hTfinish ▸ hxW) (hTfinish ▸ hxY)
    simpa only [hTfinish] using hbound
  · have hpY : p.support ⊆ Gamma.vertexSet Y := by
      intro x hxP
      by_contra hxY
      exact hx ⟨x, hxP, hxY⟩
    have hpEdgesY : p.edgeSet ⊆ familyEdges Y := by
      intro e he
      have hends := p.edgeSet_subset_support_prod he
      exact hinternal he (hpY hends.1) (hpY hends.2)
    apply (forward_support_subset_owner_at_point hY p hne hpEdgesY p.start_mem_support).trans
    apply finiteSaturationCarrier_referenceClosed hW hY J
    exact hjoin ▸ hQH ⟨Fin.last Q.length, rfl⟩

#print axioms safe_endpoint_owner_subset_saturation
#print axioms source_owner_subset_saturation
#print axioms safeTerminal_owner_subset_saturation
#print axioms forward_support_subset_saturation

end Erdos599.Alternating.ColouredSafeAuxiliaryForwardContainment
