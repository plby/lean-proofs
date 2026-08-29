/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualColorIsolation
import ErdosProblems.Erdos599.SingularMarkedResidualFiniteFactor
import ErdosProblems.Erdos599.SingularToggleExactRelation

/-!
# Realizing a marked switch while fixing every untouched designated path

A finite marked route can meet only finitely many members of the designated
warp.  The one-hole decomposition may therefore be performed after removing
all untouched designated members.  Since every route edge and every member
of the localized old family avoids the untouched carrier, the decomposed
family is disjoint from it.  Re-inserting the untouched members gives a
one-point augmentation of the original union and fixes those members
literally.

This is the finite-support form of the mixed-colour switch.  It does not
assert the false claim that the decomposed paths retain the two old endpoint
colours; it records instead the exact finite set of designated components on
which any subsequent colour repair has to act.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualLocalizedRealization

open DWeb Alternating
open SingularMarkedResidualColorIsolation
  SingularMarkedResidualFiniteFactor
  SingularMarkedResidualTouchedPaths

universe u

variable {V : Type u}

private theorem clean_subfamily
    {G : DWeb V} {J Y : Set G.DPath}
    (hJ : G.IsCleanFiniteWarp J) (hY : Y ⊆ J) :
    G.IsCleanFiniteWarp Y := by
  have hYwarp : G.IsWarp Y := fun p hp q hq hpq ↦
    hJ.1 (hY hp) (hY hq) hpq
  have hYfinite : G.HasFiniteCharacter Y := by
    intro p hp
    exact hJ.2.1 (hY hp)
  refine ⟨hYwarp, hYfinite, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hpY, hxp⟩, hxSource⟩
      have hxInitialJ : x ∈ G.initialSet J := by
        rw [← hJ.2.2.1]
        exact ⟨⟨p, hY hpY, hxp⟩, hxSource⟩
      obtain ⟨q, hqJ, hqx⟩ := hxInitialJ
      have hpq : p = q := by
        apply DWeb.IsWarp.eq_of_mem_support hJ.isWarp (hY hpY) hqJ
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
        apply DWeb.IsWarp.eq_of_mem_support hJ.isWarp (hY hpY) hqJ
        · exact hxp
        · exact G.terminal_mem_support hqx
      subst q
      exact ⟨p, hpY, hqx⟩
    · rintro x ⟨p, hpY, hpx⟩
      exact ⟨⟨p, hpY, G.terminal_mem_support hpx⟩,
        DWeb.IsCleanFiniteWarp.terminalFrontier_subset_target G hJ
          ⟨p, hY hpY, hpx⟩⟩

private theorem localized_subset_union
    (G : DWeb V) (P L : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    touchedDesignatedPaths G P l ∪ L ⊆ P ∪ L := by
  rintro p (hp | hp)
  · exact Or.inl (touchedDesignatedPaths_subset G P l hp)
  · exact Or.inr hp

private theorem old_union_factor
    (G : DWeb V) (P L : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    untouchedDesignatedPaths G P l ∪
        (touchedDesignatedPaths G P l ∪ L) = P ∪ L := by
  calc
    untouchedDesignatedPaths G P l ∪
        (touchedDesignatedPaths G P l ∪ L) =
      (untouchedDesignatedPaths G P l ∪
        touchedDesignatedPaths G P l) ∪ L := Set.union_assoc _ _ _ |>.symm
    _ = P ∪ L := by rw [untouched_union_touched]

private theorem disjoint_untouched_localized
    {G : DWeb V} {P L : Set G.DPath}
    (hP : G.IsWarp P)
    (hPL : Disjoint (G.vertexSet P) (G.vertexSet L))
    (l : List (OneHoleResidualState V)) :
    Disjoint
      (G.vertexSet (untouchedDesignatedPaths G P l))
      (G.vertexSet (touchedDesignatedPaths G P l ∪ L)) := by
  rw [G.vertexSet_union, Set.disjoint_union_right]
  constructor
  · exact (disjoint_vertexSet_touched_untouched hP l).symm
  · rw [Set.disjoint_left]
    intro x hxR hxL
    obtain ⟨p, hpR, hxp⟩ := hxR
    exact Set.disjoint_left.1 hPL
      ⟨p, untouchedDesignatedPaths_subset G P l hpR, hxp⟩ hxL

private theorem toggled_localized_avoids_untouched
    {G : DWeb V} {P L : Set G.DPath}
    (hP : G.IsWarp P)
    (hPL : Disjoint (G.vertexSet P) (G.vertexSet L))
    (l : List (OneHoleResidualState V)) :
    oneHoleRouteToggledEdges G
        (touchedDesignatedPaths G P l ∪ L) l ⊆
      (G.vertexSet (untouchedDesignatedPaths G P l))ᶜ ×ˢ
        (G.vertexSet (untouchedDesignatedPaths G P l))ᶜ := by
  let R := untouchedDesignatedPaths G P l
  let T := touchedDesignatedPaths G P l
  have hlocal : Disjoint (G.vertexSet R) (G.vertexSet (T ∪ L)) :=
    disjoint_untouched_localized hP hPL l
  rintro e (heOld | heForward)
  · have heVertices := familyEdges_subset_vertexSet_prod (T ∪ L) heOld.1
    exact ⟨
      fun heR ↦ Set.disjoint_left.1 hlocal heR heVertices.1,
      fun heR ↦ Set.disjoint_left.1 hlocal heR heVertices.2⟩
  · rcases heForward with ⟨i, hi, rfl⟩
    exact ⟨
      route_state_avoids_untouched
        (List.getElem_mem (show i.1 < l.length by omega)),
      route_state_avoids_untouched
        (List.getElem_mem (show i.1 + 1 < l.length by omega))⟩

private theorem isWarp_union_of_disjoint_vertexSet
    {G : DWeb V} {R W : Set G.DPath}
    (hR : G.IsWarp R) (hW : G.IsWarp W)
    (hdisjoint : Disjoint (G.vertexSet R) (G.vertexSet W)) :
    G.IsWarp (R ∪ W) := by
  intro p hp q hq hpq
  rcases hp with hpR | hpW <;> rcases hq with hqR | hqW
  · exact hR hpR hqR hpq
  · change Disjoint p.support q.support
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.1 hdisjoint
      ⟨p, hpR, hxp⟩ ⟨q, hqW, hxq⟩
  · change Disjoint p.support q.support
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.1 hdisjoint
      ⟨q, hqR, hxq⟩ ⟨p, hpW, hxp⟩
  · exact hW hpW hqW hpq

private theorem finiteCharacter_union
    {G : DWeb V} {R W : Set G.DPath}
    (hR : G.HasFiniteCharacter R) (hW : G.HasFiniteCharacter W) :
    G.HasFiniteCharacter (R ∪ W) := by
  intro p hp
  rcases hp with hpR | hpW
  · exact hR hpR
  · exact hW hpW

/-- A marked one-hole augmentation can be realized by changing only the
finitely many designated paths met by the route.  All untouched designated
members occur literally in the global output. -/
theorem exists_onePointAugmentation_fixing_untouched_exactRelation
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hP : G.IsWarp P)
    (hPL : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hJ : G.IsCleanFiniteWarp (P ∪ L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∈ G.source \ G.initialSet (P ∪ L))
    (hb : b ∈ G.target \ G.terminalFrontier (P ∪ L))
    (hab : a ≠ b) :
    ∃ JlocalPlus : Set G.DPath,
      G.IsOnePointAugmentation
        (touchedDesignatedPaths G P l ∪ L) JlocalPlus ∧
      Disjoint
        (G.vertexSet (untouchedDesignatedPaths G P l))
        (G.vertexSet JlocalPlus) ∧
      G.IsOnePointAugmentation (P ∪ L)
        (untouchedDesignatedPaths G P l ∪ JlocalPlus) ∧
      G.initialSet JlocalPlus =
        insert a (G.initialSet (touchedDesignatedPaths G P l ∪ L)) ∧
      G.terminalFrontier JlocalPlus =
        insert b (G.terminalFrontier
          (touchedDesignatedPaths G P l ∪ L)) ∧
      ∃ C : Cyclowarp G,
        JlocalPlus = C.pathPart ∧
        C.edges = oneHoleRouteToggledEdges G
          (touchedDesignatedPaths G P l ∪ L) l ∧
        C.isolated = isolatedVertices
          (touchedDesignatedPaths G P l ∪ L) := by
  let R := untouchedDesignatedPaths G P l
  let T := touchedDesignatedPaths G P l
  let Jlocal := T ∪ L
  have hJlocalSub : Jlocal ⊆ P ∪ L :=
    localized_subset_union G P L l
  have hJlocal : G.IsCleanFiniteWarp Jlocal :=
    clean_subfamily hJ hJlocalSub
  have hlLocal : IsReducedMarkedRoute G Jlocal a b l := by
    exact reducedRoute_localize_designated hl
  have haLocal : a ∈ G.source \ G.initialSet Jlocal := by
    refine ⟨ha.1, ?_⟩
    intro haLocal
    obtain ⟨p, hpLocal, hpa⟩ := haLocal
    exact ha.2 ⟨p, hJlocalSub hpLocal, hpa⟩
  have hbLocal : b ∈ G.target \ G.terminalFrontier Jlocal := by
    refine ⟨hb.1, ?_⟩
    intro hbLocal
    obtain ⟨p, hpLocal, hpb⟩ := hbLocal
    exact hb.2 ⟨p, hJlocalSub hpLocal, hpb⟩
  let toggle : OneHoleToggleCertificate G Jlocal a b :=
    oneHoleToggleCertificateOfReducedRoute hJlocal haLocal hlLocal
      (oneHoleRouteBalance G Jlocal a b l hJlocal haLocal hlLocal)
  have htoggleAvoid : toggle.edges ⊆
      (G.vertexSet R)ᶜ ×ˢ (G.vertexSet R)ᶜ := by
    change oneHoleRouteToggledEdges G Jlocal l ⊆
      (G.vertexSet R)ᶜ ×ˢ (G.vertexSet R)ᶜ
    exact toggled_localized_avoids_untouched hP hPL l
  have hRlocal : Disjoint (G.vertexSet R) (G.vertexSet Jlocal) :=
    disjoint_untouched_localized hP hPL l
  obtain ⟨JlocalPlus, hlocalPlus, hRplus, hinitLocal, htermLocal,
      C, hCpath, hCedges, hCisolated⟩ :=
    SingularToggleExactRelation.exists_onePointAugmentation_of_toggleCertificate_avoiding_exactRelation
        G hJlocal haLocal hbLocal hab toggle (G.vertexSet R)
          htoggleAvoid hRlocal
  have hglobal : G.IsOnePointAugmentation (P ∪ L)
      (R ∪ JlocalPlus) := by
    obtain ⟨a', ha', b', hb', hplusWarp, hplusFinite,
        hplusInitial, hplusTerminal⟩ := hlocalPlus
    have haa' : a' = a := by
      have ha'New : a' ∈ insert a (G.initialSet Jlocal) := by
        rw [← hinitLocal, hplusInitial]
        exact Or.inl rfl
      rcases ha'New with ha'eq | ha'Old
      · exact ha'eq
      · exact False.elim (ha'.2 ha'Old)
    have hbb' : b' = b := by
      have hb'New : b' ∈ insert b (G.terminalFrontier Jlocal) := by
        rw [← htermLocal, hplusTerminal]
        exact Or.inl rfl
      rcases hb'New with hb'eq | hb'Old
      · exact hb'eq
      · exact False.elim (hb'.2 hb'Old)
    subst a'
    subst b'
    refine ⟨a, ha, b, hb, ?_, ?_, ?_, ?_⟩
    · exact isWarp_union_of_disjoint_vertexSet
        (fun p hp q hq hpq ↦ hP (untouchedDesignatedPaths_subset G P l hp)
          (untouchedDesignatedPaths_subset G P l hq) hpq)
        hplusWarp hRplus
    · exact finiteCharacter_union
        (by
          intro p hp
          exact hJ.2.1
            (Or.inl (untouchedDesignatedPaths_subset G P l hp)))
        hplusFinite
    · rw [G.initialSet_union, hinitLocal]
      rw [show G.initialSet R ∪ insert a (G.initialSet Jlocal) =
          insert a (G.initialSet R ∪ G.initialSet Jlocal) by
        ext x
        simp only [Set.mem_union, Set.mem_insert_iff]
        tauto]
      rw [← G.initialSet_union, old_union_factor]
    · rw [G.terminalFrontier_union, htermLocal]
      rw [show G.terminalFrontier R ∪ insert b (G.terminalFrontier Jlocal) =
          insert b (G.terminalFrontier R ∪ G.terminalFrontier Jlocal) by
        ext x
        simp only [Set.mem_union, Set.mem_insert_iff]
        tauto]
      rw [← G.terminalFrontier_union, old_union_factor]

  exact ⟨JlocalPlus, hlocalPlus, hRplus, hglobal,
    by simpa only using hinitLocal, by simpa only using htermLocal,
    C, hCpath, hCedges, hCisolated⟩

/-- Backward-compatible exact-endpoint wrapper, forgetting the cyclowarp
which realizes the exact toggled edge relation. -/
theorem exists_onePointAugmentation_fixing_untouched_exact
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hP : G.IsWarp P)
    (hPL : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hJ : G.IsCleanFiniteWarp (P ∪ L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∈ G.source \ G.initialSet (P ∪ L))
    (hb : b ∈ G.target \ G.terminalFrontier (P ∪ L))
    (hab : a ≠ b) :
    ∃ JlocalPlus : Set G.DPath,
      G.IsOnePointAugmentation
        (touchedDesignatedPaths G P l ∪ L) JlocalPlus ∧
      Disjoint
        (G.vertexSet (untouchedDesignatedPaths G P l))
        (G.vertexSet JlocalPlus) ∧
      G.IsOnePointAugmentation (P ∪ L)
        (untouchedDesignatedPaths G P l ∪ JlocalPlus) ∧
      G.initialSet JlocalPlus =
        insert a (G.initialSet (touchedDesignatedPaths G P l ∪ L)) ∧
      G.terminalFrontier JlocalPlus =
        insert b (G.terminalFrontier
          (touchedDesignatedPaths G P l ∪ L)) := by
  obtain ⟨JlocalPlus, hlocal, hdisjoint, hglobal, hinit, hterminal,
      _C, _hCpath, _hCedges, _hCisolated⟩ :=
    exists_onePointAugmentation_fixing_untouched_exactRelation
      hP hPL hJ hl ha hb hab
  exact ⟨JlocalPlus, hlocal, hdisjoint, hglobal, hinit, hterminal⟩

/-- Endpoint-erased compatibility wrapper for the localized realization. -/
theorem exists_onePointAugmentation_fixing_untouched
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hP : G.IsWarp P)
    (hPL : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hJ : G.IsCleanFiniteWarp (P ∪ L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∈ G.source \ G.initialSet (P ∪ L))
    (hb : b ∈ G.target \ G.terminalFrontier (P ∪ L))
    (hab : a ≠ b) :
    ∃ JlocalPlus : Set G.DPath,
      G.IsOnePointAugmentation
        (touchedDesignatedPaths G P l ∪ L) JlocalPlus ∧
      Disjoint
        (G.vertexSet (untouchedDesignatedPaths G P l))
        (G.vertexSet JlocalPlus) ∧
      G.IsOnePointAugmentation (P ∪ L)
        (untouchedDesignatedPaths G P l ∪ JlocalPlus) := by
  obtain ⟨JlocalPlus, hlocal, hdisjoint, hglobal, _hinit, _hterminal⟩ :=
    exists_onePointAugmentation_fixing_untouched_exact
      hP hPL hJ hl ha hb hab
  exact ⟨JlocalPlus, hlocal, hdisjoint, hglobal⟩

#print axioms exists_onePointAugmentation_fixing_untouched_exact
#print axioms exists_onePointAugmentation_fixing_untouched_exactRelation
#print axioms exists_onePointAugmentation_fixing_untouched

end SingularMarkedResidualLocalizedRealization
end CardinalInduction
end Erdos599
