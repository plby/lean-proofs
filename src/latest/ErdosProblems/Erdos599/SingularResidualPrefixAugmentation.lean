/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualContactBlocks
import ErdosProblems.Erdos599.OneHoleRouteBalance

/-!
# Realizing the residual prefix before the first designated contact

The ordered mixed route has a shortest prefix which uses only the residual
colour and ends at the first vertex of the designated carrier.  After adding
that boundary vertex to the target, this prefix is an ordinary one-point
augmentation of the residual warp.  This retains the complete route-order
information: it is stronger than an endpoint count for an arbitrary mixed
augmentation and is the input for a first-hit deletion at the boundary.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularResidualPrefixAugmentation

open DWeb Alternating
open SingularMarkedResidualColorOrder
  SingularMarkedResidualContactBlocks

universe u

variable {V : Type u}

private theorem right_mem_vertexSet_of_familyEdge
    {G : DWeb V} {W : Set G.DPath} {x y : V}
    (hxy : (x, y) ∈ familyEdges W) : y ∈ G.vertexSet W := by
  simp only [familyEdges, Set.mem_iUnion] at hxy
  obtain ⟨p, hpW, hpedge⟩ := hxy
  exact ⟨p, hpW, (p.edgeSet_subset_support_prod hpedge).2⟩

/-- Adding a vertex avoided by a clean finite warp to the target preserves
cleanliness. -/
theorem cleanFiniteWarp_retarget_insert_of_avoids
    {G : DWeb V} {L : Set G.DPath} {x : V}
    (hL : G.IsCleanFiniteWarp L) (hx : x ∉ G.vertexSet L) :
    (G.retarget (insert x G.target)).IsCleanFiniteWarp L := by
  let H := G.retarget (insert x G.target)
  refine ⟨hL.isWarp, hL.hasFiniteCharacter, ?_, ?_⟩
  · change G.vertexSet L ∩ G.source = G.initialSet L
    exact hL.2.2.1
  · change G.vertexSet L ∩ insert x G.target = G.terminalFrontier L
    rw [← hL.2.2.2]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨hyL, rfl | hyTarget⟩
      · exact False.elim (hx hyL)
      · exact ⟨hyL, hyTarget⟩
    · exact fun hy ↦ ⟨hy.1, Or.inr hy.2⟩

/-- Before its first designated cancellation, a mixed residual route can be
realized as an exact residual one-point augmentation whose new terminal is
the first designated-carrier contact. -/
theorem exists_residualPrefixOnePointAugmentation
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hPL : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hL : G.IsCleanFiniteWarp L)
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∈ G.source \ G.initialSet (P ∪ L))
    (haP : a ∉ G.vertexSet P) (hbP : b ∉ G.vertexSet P)
    (hcontact : ¬ Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P)) :
    ∃ x : V, x ∈ G.vertexSet P ∧
      ∃ prefixRoute : List (OneHoleResidualState V),
        IsReducedMarkedRoute G L a x prefixRoute ∧
        ∃ Lplus : Set G.DPath,
          (G.retarget (insert x G.target)).IsOnePointAugmentation L Lplus := by
  obtain ⟨i, _j, x, _y, hi, _hfirst, hsourceX, _hj, _hlast, _hij,
      _htargetY, prefixRoute, _suffixRoute, hprefix, _hsuffix⟩ :=
    exists_reducedResidualOuterRoutes hPL hl haP hbP hcontact
  have hxP : x ∈ G.vertexSet P := by
    have hx := right_mem_vertexSet_of_familyEdge hi.2
    rw [hsourceX] at hx
    exact hx
  have hxL : x ∉ G.vertexSet L := fun hxL ↦
    Set.disjoint_left.1 hPL hxP hxL
  let H := G.retarget (insert x G.target)
  have hLH : H.IsCleanFiniteWarp L :=
    cleanFiniteWarp_retarget_insert_of_avoids hL hxL
  have hprefixH : IsReducedMarkedRoute H L a x prefixRoute := by
    change IsReducedMarkedRoute G L a x prefixRoute
    exact hprefix
  have haL : a ∈ H.source \ H.initialSet L := by
    refine ⟨ha.1, ?_⟩
    intro haL
    apply ha.2
    rw [G.initialSet_union]
    exact Or.inr haL
  have hxTerminal : x ∈ H.target \ H.terminalFrontier L := by
    refine ⟨Or.inl rfl, ?_⟩
    rintro ⟨p, hpL, hpx⟩
    exact hxL ⟨p, hpL, G.terminal_mem_support hpx⟩
  have hax : a ≠ x := by
    intro hax
    subst x
    exact haP hxP
  let T : OneHoleToggleCertificate H L a x :=
    oneHoleToggleCertificateOfReducedRoute hLH haL hprefixH
      (oneHoleRouteBalance H L a x prefixRoute hLH haL hprefixH)
  obtain ⟨Lplus, hplus⟩ :=
    exists_onePointAugmentation_of_toggleCertificate
      H hLH haL hxTerminal hax T
  exact ⟨x, hxP, prefixRoute, hprefix, Lplus, hplus⟩

#print axioms cleanFiniteWarp_retarget_insert_of_avoids
#print axioms exists_residualPrefixOnePointAugmentation

end SingularResidualPrefixAugmentation
end CardinalInduction
end Erdos599
