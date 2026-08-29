/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualTouchedPaths
import ErdosProblems.Erdos599.SingularMarkedResidualColorIsolation

/-!
# Factoring the untouched designated colour out of a marked toggle

After localizing a finite marked route to its touched designated components,
the untouched designated paths are completely inert.  They avoid every route
state, their carriers are disjoint from both the touched designated family
and the residual family, and their edge relation factors literally out of the
route toggle.

Thus the genuinely mixed switching problem is finite on the designated side:
the global toggled relation is the disjoint union of the unchanged untouched
designated relation and the toggle of `touchedDesignatedPaths ∪ L`.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualFiniteFactor

open DWeb Alternating
open SingularMarkedResidualTouchedPaths
open SingularMarkedResidualColorOrder
open SingularMarkedResidualColorIsolation

universe u

variable {V : Type u}

private theorem cleanFiniteWarp_subfamily
    {G : DWeb V} {J Y : Set G.DPath}
    (hJ : G.IsCleanFiniteWarp J) (hY : Y ⊆ J) :
    G.IsCleanFiniteWarp Y := by
  have hYwarp : G.IsWarp Y := fun p hp q hq hpq ↦
    hJ.1 (hY hp) (hY hq) hpq
  have hYfin : G.HasFiniteCharacter Y := by
    intro p hp
    exact hJ.2.1 (hY hp)
  refine ⟨hYwarp, hYfin, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hpY, hxp⟩, hxSource⟩
      have hxInitialJ : x ∈ G.initialSet J := by
        rw [← hJ.2.2.1]
        exact ⟨⟨p, hY hpY, hxp⟩, hxSource⟩
      obtain ⟨q, hqJ, hqx⟩ := hxInitialJ
      have hpq : p = q := by
        apply DWeb.IsWarp.eq_of_mem_support hJ.1 (hY hpY) hqJ
        · exact hxp
        · exact hqx ▸ q.initial_mem_support
      subst q
      exact ⟨p, hpY, hqx⟩
    · rintro x ⟨p, hpY, rfl⟩
      exact ⟨⟨p, hpY, p.initial_mem_support⟩,
        DWeb.IsCleanFiniteWarp.initialSet_subset_source G hJ
          ⟨p, hY hpY, rfl⟩⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hpY, hxp⟩, hxTarget⟩
      have hxTerminalJ : x ∈ G.terminalFrontier J := by
        rw [← hJ.2.2.2]
        exact ⟨⟨p, hY hpY, hxp⟩, hxTarget⟩
      obtain ⟨q, hqJ, hqx⟩ := hxTerminalJ
      have hpq : p = q := by
        apply DWeb.IsWarp.eq_of_mem_support hJ.1 (hY hpY) hqJ
        · exact hxp
        · exact G.terminal_mem_support hqx
      subst q
      exact ⟨p, hpY, hqx⟩
    · rintro x ⟨p, hpY, hpx⟩
      exact ⟨⟨p, hpY, G.terminal_mem_support hpx⟩,
        DWeb.IsCleanFiniteWarp.terminalFrontier_subset_target G hJ
          ⟨p, hY hpY, hpx⟩⟩

/-- The designated components not met by the marked route. -/
def untouchedDesignatedPaths
    (G : DWeb V) (P : Set G.DPath)
    (l : List (OneHoleResidualState V)) : Set G.DPath :=
  P \ touchedDesignatedPaths G P l

theorem untouchedDesignatedPaths_subset
    (G : DWeb V) (P : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    untouchedDesignatedPaths G P l ⊆ P :=
  Set.diff_subset

/-- Every designated component is either untouched or touched. -/
theorem untouched_union_touched
    (G : DWeb V) (P : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    untouchedDesignatedPaths G P l ∪
      touchedDesignatedPaths G P l = P := by
  ext p
  simp only [untouchedDesignatedPaths, Set.mem_union, Set.mem_diff,
    mem_pathsMeetingVertices]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩)
    · exact hp
    · exact hp
  · intro hp
    by_cases ht : p ∈ touchedDesignatedPaths G P l
    · exact Or.inr ht
    · exact Or.inl ⟨hp, ht⟩

/-- No route state lies on an untouched designated path. -/
theorem route_state_avoids_untouched
    {G : DWeb V} {P : Set G.DPath}
    {l : List (OneHoleResidualState V)}
    {s : OneHoleResidualState V} (hs : s ∈ l) :
    s.vertex ∉ G.vertexSet (untouchedDesignatedPaths G P l) := by
  rintro ⟨p, hpR, hsp⟩
  apply hpR.2
  exact ⟨hpR.1, s.vertex, hsp, state_vertex_mem_routeVertexSet hs⟩

/-- A warp separates the carriers of its touched and untouched subfamilies. -/
theorem disjoint_vertexSet_touched_untouched
    {G : DWeb V} {P : Set G.DPath} (hP : G.IsWarp P)
    (l : List (OneHoleResidualState V)) :
    Disjoint
      (G.vertexSet (touchedDesignatedPaths G P l))
      (G.vertexSet (untouchedDesignatedPaths G P l)) := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hpT, hxp⟩ ⟨q, hqR, hxq⟩
  have hpP := touchedDesignatedPaths_subset G P l hpT
  have hqP := untouchedDesignatedPaths_subset G P l hqR
  by_cases hpq : p = q
  · subst q
    exact hqR.2 hpT
  · exact Set.disjoint_left.1 (hP hpP hqP hpq) hxp hxq

/-- Disjointness from the whole designated carrier descends to its untouched
subfamily. -/
theorem disjoint_vertexSet_residual_untouched
    {G : DWeb V} {P L : Set G.DPath}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (l : List (OneHoleResidualState V)) :
    Disjoint (G.vertexSet L)
      (G.vertexSet (untouchedDesignatedPaths G P l)) := by
  rw [Set.disjoint_left]
  intro x hxL hxR
  exact Set.disjoint_left.1 hdisjoint
    (by
      obtain ⟨p, hpR, hxp⟩ := hxR
      exact ⟨p, untouchedDesignatedPaths_subset G P l hpR, hxp⟩)
    hxL

/-- Every inserted forward route edge avoids the untouched designated
carrier at both ends. -/
theorem forwardEdges_avoid_untouched
    (G : DWeb V) (P L : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    oneHoleRouteForwardEdges G (P ∪ L) l ⊆
      (G.vertexSet (untouchedDesignatedPaths G P l))ᶜ ×ˢ
        (G.vertexSet (untouchedDesignatedPaths G P l))ᶜ := by
  rintro e ⟨i, hi, rfl⟩
  constructor
  · apply route_state_avoids_untouched
    exact List.getElem_mem (show i.1 < l.length by omega)
  · apply route_state_avoids_untouched
    exact List.getElem_mem (show i.1 + 1 < l.length by omega)

private theorem familyEdges_union
    (G : DWeb V) (P L : Set G.DPath) :
    familyEdges (P ∪ L) = familyEdges P ∪ familyEdges L := by
  ext e
  simp only [familyEdges, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨p, hp | hp, he⟩
    · exact Or.inl ⟨p, hp, he⟩
    · exact Or.inr ⟨p, hp, he⟩
  · rintro (⟨p, hp, he⟩ | ⟨p, hp, he⟩)
    · exact ⟨p, Or.inl hp, he⟩
    · exact ⟨p, Or.inr hp, he⟩

theorem familyEdges_designated_factor
    (G : DWeb V) (P : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    familyEdges P =
      familyEdges (untouchedDesignatedPaths G P l) ∪
        familyEdges (touchedDesignatedPaths G P l) := by
  rw [← familyEdges_union, untouched_union_touched]

private theorem chosenBackward_localize_iff
    {G : DWeb V} {P L : Set G.DPath}
    {l : List (OneHoleResidualState V)}
    {s t : OneHoleResidualState V}
    (hs : s ∈ l) (ht : t ∈ l) :
    OneHoleChosenBackwardStep G (P ∪ L) s t ↔
      OneHoleChosenBackwardStep G
        (touchedDesignatedPaths G P l ∪ L) s t := by
  have hsRoute := state_vertex_mem_routeVertexSet hs
  have htRoute := state_vertex_mem_routeVertexSet ht
  have hst := familyEdge_touched_iff_of_left_route_vertex
    (P := P) (l := l) hsRoute (y := t.vertex)
  have hts := familyEdge_touched_iff_of_left_route_vertex
    (P := P) (l := l) htRoute (y := s.vertex)
  have htCarrier := route_vertex_mem_vertexSet_touched_iff
    (G := G) (P := P) htRoute
  cases s <;> cases t <;>
    simp only [OneHoleResidualState.vertex_ready,
      OneHoleResidualState.vertex_pending] at hst hts htCarrier <;>
    simp only [OneHoleChosenBackwardStep, OneHoleChosenForwardStep,
      familyEdges_union, G.vertexSet_union, Set.mem_union] <;>
    tauto

private theorem chosenForward_localize_iff
    {G : DWeb V} {P L : Set G.DPath}
    {l : List (OneHoleResidualState V)}
    {s t : OneHoleResidualState V}
    (hs : s ∈ l) (ht : t ∈ l) :
    OneHoleChosenForwardStep G (P ∪ L) s t ↔
      OneHoleChosenForwardStep G
        (touchedDesignatedPaths G P l ∪ L) s t := by
  have hsRoute := state_vertex_mem_routeVertexSet hs
  have htRoute := state_vertex_mem_routeVertexSet ht
  have hst := familyEdge_touched_iff_of_left_route_vertex
    (P := P) (l := l) hsRoute (y := t.vertex)
  have htCarrier := route_vertex_mem_vertexSet_touched_iff
    (G := G) (P := P) htRoute
  cases s <;> cases t <;>
    simp only [OneHoleResidualState.vertex_ready,
      OneHoleResidualState.vertex_pending] at hst htCarrier <;>
    simp only [OneHoleChosenForwardStep, familyEdges_union,
      G.vertexSet_union, Set.mem_union] <;>
    tauto

/-- The chosen backward edge set is unchanged by finite localization. -/
theorem backwardEdges_localize_designated
    (G : DWeb V) (P L : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    oneHoleRouteBackwardEdges G (P ∪ L) l =
      oneHoleRouteBackwardEdges G
        (touchedDesignatedPaths G P l ∪ L) l := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    apply (chosenBackward_localize_iff
      (List.getElem_mem (show i.1 < l.length by omega))
      (List.getElem_mem (show i.1 + 1 < l.length by omega))).mp
    exact hi
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    apply (chosenBackward_localize_iff
      (List.getElem_mem (show i.1 < l.length by omega))
      (List.getElem_mem (show i.1 + 1 < l.length by omega))).mpr
    exact hi

/-- The chosen forward edge set is unchanged by finite localization. -/
theorem forwardEdges_localize_designated
    (G : DWeb V) (P L : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    oneHoleRouteForwardEdges G (P ∪ L) l =
      oneHoleRouteForwardEdges G
        (touchedDesignatedPaths G P l ∪ L) l := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    apply (chosenForward_localize_iff
      (List.getElem_mem (show i.1 < l.length by omega))
      (List.getElem_mem (show i.1 + 1 < l.length by omega))).mp
    exact hi
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    apply (chosenForward_localize_iff
      (List.getElem_mem (show i.1 < l.length by omega))
      (List.getElem_mem (show i.1 + 1 < l.length by omega))).mpr
    exact hi

/-- No deleted backward edge belongs to an untouched designated component. -/
theorem backwardEdges_disjoint_untouched
    {G : DWeb V} {P L : Set G.DPath} (hP : G.IsWarp P)
    (l : List (OneHoleResidualState V)) :
    Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l)
      (familyEdges (untouchedDesignatedPaths G P l)) := by
  rw [Set.disjoint_left]
  intro e heBackward heR
  have heP : e ∈ familyEdges P := by
    simp only [familyEdges, Set.mem_iUnion] at heR ⊢
    obtain ⟨p, hpR, he⟩ := heR
    exact ⟨p, untouchedDesignatedPaths_subset G P l hpR, he⟩
  have heT : e ∈ familyEdges (touchedDesignatedPaths G P l) :=
    designated_backwardEdges_subset_familyEdges_touched G P L l
      ⟨heBackward, heP⟩
  have hcarrier := disjoint_vertexSet_touched_untouched hP l
  have hedgeDisjoint :=
    disjoint_familyEdges_of_disjoint_vertexSet hcarrier
  exact Set.disjoint_left.1 hedgeDisjoint heT heR

/-- The untouched designated edge relation factors literally out of the
global marked toggle. -/
theorem toggledEdges_factor_untouched
    {G : DWeb V} {P L : Set G.DPath} (hP : G.IsWarp P)
    (l : List (OneHoleResidualState V)) :
    oneHoleRouteToggledEdges G (P ∪ L) l =
      familyEdges (untouchedDesignatedPaths G P l) ∪
        oneHoleRouteToggledEdges G
          (touchedDesignatedPaths G P l ∪ L) l := by
  let R := untouchedDesignatedPaths G P l
  let T := touchedDesignatedPaths G P l
  have hfamily : familyEdges (P ∪ L) =
      familyEdges R ∪ familyEdges (T ∪ L) := by
    rw [familyEdges_union, familyEdges_designated_factor,
      familyEdges_union]
    ext e
    simp only [Set.mem_union]
    tauto
  have hback := backwardEdges_localize_designated G P L l
  have hforward := forwardEdges_localize_designated G P L l
  have hdisjoint := backwardEdges_disjoint_untouched (L := L) hP l
  ext e
  simp only [oneHoleRouteToggledEdges, hfamily, hback, hforward,
    Set.mem_union, Set.mem_diff]
  have hnotBoth : ¬(e ∈ oneHoleRouteBackwardEdges G (T ∪ L) l ∧
      e ∈ familyEdges R) := by
    intro h
    exact Set.disjoint_left.1 hdisjoint (hback.symm ▸ h.1) h.2
  tauto

/-! ## A confined mixed augmentation -/

/-- The global marked route can be switched after first factoring out every
untouched designated component.  The resulting one-point augmentation only
modifies `touchedDesignatedPaths G P l ∪ L`, and its entire new carrier stays
disjoint from the unchanged designated remainder.

The designated part of the old family occurring in the switch is finite by
`touchedDesignatedPaths_finite`; no finiteness assumption on the residual
colour is needed beyond the finite-character field of the clean old warp. -/
theorem exists_localized_onePointAugmentation_avoiding_untouched_exact
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hP : G.IsWarp P)
    (hPL : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hclean : G.IsCleanFiniteWarp (P ∪ L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∈ G.source \ G.initialSet (P ∪ L))
    (hb : b ∈ G.target \ G.terminalFrontier (P ∪ L))
    (hab : a ≠ b) :
    let T := touchedDesignatedPaths G P l
    let R := untouchedDesignatedPaths G P l
    ∃ Qplus, G.IsOnePointAugmentation (T ∪ L) Qplus ∧
      Disjoint (G.vertexSet R) (G.vertexSet Qplus) ∧
      G.initialSet Qplus = insert a (G.initialSet (T ∪ L)) ∧
      G.terminalFrontier Qplus =
        insert b (G.terminalFrontier (T ∪ L)) := by
  let T := touchedDesignatedPaths G P l
  let R := untouchedDesignatedPaths G P l
  have hdecomp : P ∪ L = R ∪ (T ∪ L) := by
    rw [← Set.union_assoc, untouched_union_touched]
  have hR_TL : Disjoint (G.vertexSet R) (G.vertexSet (T ∪ L)) := by
    rw [G.vertexSet_union, Set.disjoint_union_right]
    constructor
    · exact (disjoint_vertexSet_touched_untouched hP l).symm
    · rw [Set.disjoint_left]
      intro x hxR hxL
      apply Set.disjoint_left.1 hPL
      · obtain ⟨p, hpR, hxp⟩ := hxR
        exact ⟨p, untouchedDesignatedPaths_subset G P l hpR, hxp⟩
      · exact hxL
  have hTLclean : G.IsCleanFiniteWarp (T ∪ L) := by
    apply cleanFiniteWarp_subfamily hclean
    intro p hp
    rcases hp with hpT | hpL
    · exact Or.inl (touchedDesignatedPaths_subset G P l hpT)
    · exact Or.inr hpL
  have hlDecomp : IsReducedMarkedRoute G (R ∪ (T ∪ L)) a b l := by
    rw [← hdecomp]
    exact hl
  have haR : a ∉ G.vertexSet R := by
    have hfirstMem : (OneHoleResidualState.ready a) ∈ l := by
      rw [← oneHoleRoute_first hl]
      exact List.getElem_mem (List.length_pos_iff.mpr hl.1.1)
    simpa only [R, OneHoleResidualState.vertex_ready] using
      (route_state_avoids_untouched (G := G) (P := P) hfirstMem)
  have hnoR : Disjoint
      (oneHoleRouteBackwardEdges G (R ∪ (T ∪ L)) l)
      (familyEdges R) := by
    rw [← hdecomp]
    exact backwardEdges_disjoint_untouched (L := L) hP l
  have haTL : a ∈ G.source \ G.initialSet (T ∪ L) := by
    refine ⟨ha.1, ?_⟩
    intro haTL
    apply ha.2
    rw [hdecomp, G.initialSet_union]
    exact Or.inr haTL
  have hbTL : b ∈ G.target \ G.terminalFrontier (T ∪ L) := by
    refine ⟨hb.1, ?_⟩
    intro hbTL
    apply hb.2
    rw [hdecomp, G.terminalFrontier_union]
    exact Or.inr hbTL
  exact exists_residual_onePointAugmentation_avoiding_designated_exact
    hR_TL hTLclean hlDecomp haR hnoR haTL hbTL hab

/-- Adjoining a carrier-disjoint, unchanged warp to both sides of a
one-point augmentation preserves the augmentation equations. -/
private theorem onePointAugmentation_union_left
    {G : DWeb V} {R Q Qplus : Set G.DPath} {a b : V}
    (hRwarp : G.IsWarp R) (hRfinite : G.HasFiniteCharacter R)
    (hRQplus : Disjoint (G.vertexSet R) (G.vertexSet Qplus))
    (haR : a ∉ G.initialSet R) (hbR : b ∉ G.terminalFrontier R)
    (hplus : G.IsOnePointAugmentation Q Qplus)
    (ha : a ∈ G.source \ G.initialSet Q)
    (hb : b ∈ G.target \ G.terminalFrontier Q)
    (hinitial : G.initialSet Qplus = insert a (G.initialSet Q))
    (hterminal : G.terminalFrontier Qplus =
      insert b (G.terminalFrontier Q)) :
    G.IsOnePointAugmentation (R ∪ Q) (R ∪ Qplus) := by
  obtain ⟨_a, _ha, _b, _hb, hQplusWarp, hQplusFinite,
    _hinitial, _hterminal⟩ := hplus
  have hRQplusWarp : G.IsWarp (R ∪ Qplus) := by
    apply Set.PairwiseDisjoint.union hRwarp hQplusWarp
    intro p hpR q hqQ hpq
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.1 hRQplus
      ⟨p, hpR, hxp⟩ ⟨q, hqQ, hxq⟩
  have hRQplusFinite : G.HasFiniteCharacter (R ∪ Qplus) := by
    intro p hp
    rcases hp with hpR | hpQ
    · exact hRfinite hpR
    · exact hQplusFinite hpQ
  refine ⟨a, ?_, b, ?_, hRQplusWarp, hRQplusFinite, ?_, ?_⟩
  · refine ⟨ha.1, ?_⟩
    rw [G.initialSet_union]
    exact fun h ↦ h.elim haR ha.2
  · refine ⟨hb.1, ?_⟩
    rw [G.terminalFrontier_union]
    exact fun h ↦ h.elim hbR hb.2
  · rw [G.initialSet_union, hinitial, G.initialSet_union]
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto
  · rw [G.terminalFrontier_union, hterminal,
      G.terminalFrontier_union]
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto

/-- Finite-support global exchange: the one-point augmentation of the whole
old family can be chosen to retain every untouched designated path literally.
Only the finite designated subfamily meeting the marked route is allowed to
be rerouted. -/
theorem exists_onePointAugmentation_fixing_untouched_designated
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hP : G.IsWarp P)
    (hPL : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hclean : G.IsCleanFiniteWarp (P ∪ L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∈ G.source \ G.initialSet (P ∪ L))
    (hb : b ∈ G.target \ G.terminalFrontier (P ∪ L))
    (hab : a ≠ b) :
    let T := touchedDesignatedPaths G P l
    let R := untouchedDesignatedPaths G P l
    ∃ Jplus, G.IsOnePointAugmentation (P ∪ L) Jplus ∧
      R ⊆ Jplus ∧ T.Finite := by
  let T := touchedDesignatedPaths G P l
  let R := untouchedDesignatedPaths G P l
  obtain ⟨Qplus, hplus, hRQplus, hinitial, hterminal⟩ :=
    exists_localized_onePointAugmentation_avoiding_untouched_exact
      hP hPL hclean hl ha hb hab
  have hdecomp : P ∪ L = R ∪ (T ∪ L) := by
    rw [← Set.union_assoc, untouched_union_touched]
  have hRwarp : G.IsWarp R := by
    intro p hp q hq hpq
    exact hP
      (untouchedDesignatedPaths_subset G P l hp)
      (untouchedDesignatedPaths_subset G P l hq) hpq
  have hRfinite : G.HasFiniteCharacter R := by
    intro p hp
    apply hclean.2.1
    exact Or.inl (untouchedDesignatedPaths_subset G P l hp)
  have haR : a ∉ G.initialSet R := by
    intro haR
    apply ha.2
    rw [hdecomp, G.initialSet_union]
    exact Or.inl haR
  have hbR : b ∉ G.terminalFrontier R := by
    intro hbR
    apply hb.2
    rw [hdecomp, G.terminalFrontier_union]
    exact Or.inl hbR
  have haTL : a ∈ G.source \ G.initialSet (T ∪ L) := by
    refine ⟨ha.1, ?_⟩
    intro haTL
    apply ha.2
    rw [hdecomp, G.initialSet_union]
    exact Or.inr haTL
  have hbTL : b ∈ G.target \ G.terminalFrontier (T ∪ L) := by
    refine ⟨hb.1, ?_⟩
    intro hbTL
    apply hb.2
    rw [hdecomp, G.terminalFrontier_union]
    exact Or.inr hbTL
  let Jplus := R ∪ Qplus
  have hglobal : G.IsOnePointAugmentation (R ∪ (T ∪ L)) Jplus :=
    onePointAugmentation_union_left hRwarp hRfinite hRQplus
      haR hbR hplus haTL hbTL hinitial hterminal
  refine ⟨Jplus, ?_, Set.subset_union_left, touchedDesignatedPaths_finite hP l⟩
  rw [← hdecomp] at hglobal
  exact hglobal

#print axioms route_state_avoids_untouched
#print axioms disjoint_vertexSet_touched_untouched
#print axioms backwardEdges_localize_designated
#print axioms forwardEdges_localize_designated
#print axioms backwardEdges_disjoint_untouched
#print axioms toggledEdges_factor_untouched
#print axioms exists_localized_onePointAugmentation_avoiding_untouched_exact
#print axioms exists_onePointAugmentation_fixing_untouched_designated

end SingularMarkedResidualFiniteFactor
end CardinalInduction
end Erdos599
