/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageWeakSwitch
import ErdosProblems.Erdos599.ColouredSafeWeakSubdivision

/-!
# Adjoining the actual weak-switch reference companions

The native subdivision path alone does not account for newly touched
reference sources. This file adjoins the entire real companion family from
the checked local switch. Its carrier avoids both the old augmented warp
and the connector, so the union really is a warp, with exact new source and
terminal sets. No limiting-reference coverage or fair schedule is assumed.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

def liftRealPath (p : Gamma.DPath) : (imaginaryWeb Y kappa).DPath :=
  p.lift (fun he ↦ Or.inl he)

@[simp] theorem liftRealPath_support (p : Gamma.DPath) :
    (liftRealPath (Y := Y) (kappa := kappa) p).support = p.support :=
  Path.support_lift (D := Gamma.graph) (E := (imaginaryWeb Y kappa).graph)
    (fun he ↦ Or.inl he) p

@[simp] theorem liftRealPath_initial (p : Gamma.DPath) :
    (liftRealPath (Y := Y) (kappa := kappa) p).initial = p.initial := by
  cases p <;> rfl

@[simp] theorem liftRealPath_terminal (p : Gamma.DPath) :
    (liftRealPath (Y := Y) (kappa := kappa) p).terminal? = p.terminal? := by
  cases p <;> rfl

@[simp] theorem liftRealPath_edgeSet (p : Gamma.DPath) :
    (liftRealPath (Y := Y) (kappa := kappa) p).edgeSet = p.edgeSet := by
  rcases p with p | r
  · exact LinkageBlueprint.walk_edgeSet_lift _ p.walk
  · rfl

def liftRealFamily (P : Set Gamma.DPath) : Set (imaginaryWeb Y kappa).DPath :=
  liftRealPath '' P

theorem liftRealFamily_isWarp {P : Set Gamma.DPath} (hP : Gamma.IsWarp P) :
    (imaginaryWeb Y kappa).IsWarp (liftRealFamily P) := by
  rintro p ⟨p0, hp0, rfl⟩ q ⟨q0, hq0, rfl⟩ hne
  change Disjoint (liftRealPath p0).support (liftRealPath q0).support
  rw [liftRealPath_support, liftRealPath_support]
  exact hP hp0 hq0 (fun h ↦ hne (congrArg liftRealPath h))

theorem liftRealFamily_finiteCharacter {P : Set Gamma.DPath}
    (hP : Gamma.HasFiniteCharacter P) :
    (imaginaryWeb Y kappa).HasFiniteCharacter (liftRealFamily P) := by
  rintro p ⟨p0, hp0, rfl⟩
  obtain ⟨q, rfl⟩ := hP hp0
  exact ⟨q.lift (fun he ↦ Or.inl he), rfl⟩

@[simp] theorem liftRealFamily_vertexSet (P : Set Gamma.DPath) :
    (imaginaryWeb Y kappa).vertexSet (liftRealFamily P) = Gamma.vertexSet P := by
  ext x
  constructor
  · rintro ⟨p, ⟨p0, hp0, rfl⟩, hxp⟩
    exact ⟨p0, hp0, by simpa using hxp⟩
  · rintro ⟨p, hp, hxp⟩
    exact ⟨liftRealPath p, ⟨p, hp, rfl⟩, by simpa using hxp⟩

@[simp] theorem liftRealFamily_initialSet (P : Set Gamma.DPath) :
    (imaginaryWeb Y kappa).initialSet (liftRealFamily P) = Gamma.initialSet P := by
  ext x
  constructor
  · rintro ⟨p, ⟨p0, hp0, rfl⟩, hpx⟩
    exact ⟨p0, hp0, by simpa using hpx⟩
  · rintro ⟨p, hp, hpx⟩
    exact ⟨liftRealPath p, ⟨p, hp, rfl⟩, by simpa using hpx⟩

@[simp] theorem liftRealFamily_terminalFrontier (P : Set Gamma.DPath) :
    (imaginaryWeb Y kappa).terminalFrontier (liftRealFamily P) =
      Gamma.terminalFrontier P := by
  ext x
  constructor
  · rintro ⟨p, ⟨p0, hp0, rfl⟩, hpx⟩
    exact ⟨p0, hp0, by simpa only [DWeb.terminal?, liftRealPath_terminal] using hpx⟩
  · rintro ⟨p, hp, hpx⟩
    exact ⟨liftRealPath p, ⟨p, hp, rfl⟩,
      by simpa only [DWeb.terminal?, liftRealPath_terminal] using hpx⟩

@[simp] theorem liftRealFamily_familyEdges (P : Set Gamma.DPath) :
    familyEdges (liftRealFamily (Y := Y) (kappa := kappa) P) = familyEdges P := by
  ext e
  simp only [familyEdges, Set.mem_iUnion]
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, he⟩
    exact ⟨p, hp, by simpa using he⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨liftRealPath p, ⟨p, hp, rfl⟩, by simpa using he⟩

/-- The entire local weak transaction, not just the subdivided connector,
can be inserted in the native augmented warp. -/
theorem exists_weakSubdivision_with_companions_exact
    {Z : Set Gamma.DPath} {s t : V} {A : Occurrence Z s}
    (T : TouchedWeakSwitch A t)
    (hs : s ∉ Gamma.vertexSet Z) (ht : t ∉ Gamma.vertexSet Z)
    {W : Set (imaginaryWeb Y kappa).DPath}
    (hW : (imaginaryWeb Y kappa).IsWarp W)
    (hedge : (s, t) ∈ familyEdges W)
    (hconnector : T.connector.support ∩ (imaginaryWeb Y kappa).vertexSet W ⊆ {s, t})
    (hcompanions : Disjoint (Gamma.vertexSet T.companions)
      ((imaginaryWeb Y kappa).vertexSet W)) :
    ∃ U : Set (imaginaryWeb Y kappa).DPath,
      (imaginaryWeb Y kappa).IsWarp U ∧
      (imaginaryWeb Y kappa).initialSet U =
        (imaginaryWeb Y kappa).initialSet W ∪ Gamma.initialSet A.touchedReference ∧
      (imaginaryWeb Y kappa).terminalFrontier U =
        (imaginaryWeb Y kappa).terminalFrontier W ∪
          Gamma.terminalFrontier A.touchedReference ∧
      (imaginaryWeb Y kappa).vertexSet U =
        ((imaginaryWeb Y kappa).vertexSet W ∪ T.connector.support) ∪
          Gamma.vertexSet T.companions ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges T.paths ∧
      ∀ r : Ray (imaginaryWeb Y kappa).graph, Sum.inr r ∈ U →
        ∃ r0 : Ray (imaginaryWeb Y kappa).graph, Sum.inr r0 ∈ W ∧
          r0.edgeSet \ {(s, t)} ⊆ r.edgeSet := by
  let D := imaginaryWeb Y kappa
  let p : FinitePath D.graph := T.connector.lift (fun he ↦ Or.inl he)
  have hpV : p.support = T.connector.support := FinitePath.support_lift _ _
  have hfresh : D.vertexSet W ∩ p.support ⊆ {s, t} := by
    intro x hx
    exact hconnector ⟨hpV ▸ hx.2, hx.1⟩
  obtain ⟨U0, hU0, hU0I, hU0T, hU0V, hU0E, hU0Trace⟩ :=
    hW.exists_edgeSubdivision_with_rayTrace hedge p
      T.connector_start T.connector_finish hfresh
  rw [hpV] at hU0V
  let companions := liftRealFamily (Y := Y) (kappa := kappa) T.companions
  have hComp : D.IsWarp companions := liftRealFamily_isWarp T.companions_isWarp
  have hCompV : D.vertexSet companions = Gamma.vertexSet T.companions :=
    liftRealFamily_vertexSet _
  have hdisj : Disjoint (D.vertexSet U0) (D.vertexSet companions) := by
    rw [hU0V, hCompV, Set.disjoint_union_left]
    exact ⟨hcompanions.symm, T.companions_disjoint_connector.symm⟩
  let U := U0 ∪ companions
  have hU : D.IsWarp U := by
    intro p hp q hq hpq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact hU0 hp hq hpq
    · apply Set.disjoint_left.mpr
      intro x hxp hxq
      exact Set.disjoint_left.mp hdisj ⟨p, hp, hxp⟩ ⟨q, hq, hxq⟩
    · apply Set.disjoint_left.mpr
      intro x hxp hxq
      exact Set.disjoint_left.mp hdisj ⟨q, hq, hxq⟩ ⟨p, hp, hxp⟩
    · exact hComp hp hq hpq
  have hUI : D.initialSet U = D.initialSet U0 ∪ D.initialSet companions := by
    ext x
    change (∃ p ∈ U0 ∪ companions, p.initial = x) ↔ _
    simp only [Set.mem_union, or_and_right, exists_or]
    rfl
  have hUT : D.terminalFrontier U =
      D.terminalFrontier U0 ∪ D.terminalFrontier companions := by
    ext x
    change (∃ p ∈ U0 ∪ companions, p.terminal? = some x) ↔ _
    simp only [Set.mem_union, or_and_right, exists_or]
    rfl
  have hUV : D.vertexSet U = D.vertexSet U0 ∪ D.vertexSet companions := by
    ext x
    change (∃ p ∈ U0 ∪ companions, x ∈ p.support) ↔ _
    simp only [Set.mem_union, or_and_right, exists_or]
    rfl
  have hUE : familyEdges U = familyEdges U0 ∪ familyEdges companions := by
    ext e
    simp only [familyEdges, Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp | hp, he⟩
      · exact Or.inl ⟨p, hp, he⟩
      · exact Or.inr ⟨p, hp, he⟩
    · rintro (⟨p, hp, he⟩ | ⟨p, hp, he⟩)
      · exact ⟨p, Or.inl hp, he⟩
      · exact ⟨p, Or.inr hp, he⟩
  have hpE : p.edgeSet = T.connector.edgeSet :=
    LinkageBlueprint.walk_edgeSet_lift _ T.connector.walk
  have hTE : T.connector.edgeSet ∪ familyEdges T.companions = familyEdges T.paths := by
    ext e
    simp only [familyEdges, Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (he | ⟨q, hq, he⟩)
      · exact ⟨.inl T.connector, T.connector_mem, he⟩
      · exact ⟨q, hq.1, he⟩
    · rintro ⟨q, hq, he⟩
      by_cases heq : q = .inl T.connector
      · subst q
        exact Or.inl he
      · exact Or.inr ⟨q, ⟨hq, heq⟩, he⟩
  refine ⟨U, hU, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hUI, hU0I]
    change D.initialSet W ∪
      (imaginaryWeb Y kappa).initialSet (liftRealFamily T.companions) = _
    rw [liftRealFamily_initialSet, T.companions_initialSet hs]
  · rw [hUT, hU0T]
    change D.terminalFrontier W ∪
      (imaginaryWeb Y kappa).terminalFrontier (liftRealFamily T.companions) = _
    rw [liftRealFamily_terminalFrontier, T.companions_terminalFrontier ht]
  · rw [hUV, hU0V, hCompV]
  · rw [hUE, hU0E, hpE]
    change ((familyEdges W \ {(s, t)}) ∪ T.connector.edgeSet) ∪
      familyEdges (liftRealFamily T.companions) = _
    rw [liftRealFamily_familyEdges, Set.union_assoc, hTE]
  · intro r hr
    rcases hr with hr | hr
    · exact hU0Trace r hr
    · obtain ⟨p, hp, hpr⟩ := hr
      obtain ⟨p0, rfl⟩ := T.companions_finiteCharacter hp
      cases hpr

/-- The ray-trace interface of the exact weak transaction. -/
theorem exists_weakSubdivision_with_companions_and_rayTrace
    {Z : Set Gamma.DPath} {s t : V} {A : Occurrence Z s}
    (T : TouchedWeakSwitch A t)
    (hs : s ∉ Gamma.vertexSet Z) (ht : t ∉ Gamma.vertexSet Z)
    {W : Set (imaginaryWeb Y kappa).DPath}
    (hW : (imaginaryWeb Y kappa).IsWarp W)
    (hedge : (s, t) ∈ familyEdges W)
    (hconnector : T.connector.support ∩ (imaginaryWeb Y kappa).vertexSet W ⊆ {s, t})
    (hcompanions : Disjoint (Gamma.vertexSet T.companions)
      ((imaginaryWeb Y kappa).vertexSet W)) :
    ∃ U : Set (imaginaryWeb Y kappa).DPath,
      (imaginaryWeb Y kappa).IsWarp U ∧
      (imaginaryWeb Y kappa).initialSet U =
        (imaginaryWeb Y kappa).initialSet W ∪ Gamma.initialSet A.touchedReference ∧
      (imaginaryWeb Y kappa).terminalFrontier U =
        (imaginaryWeb Y kappa).terminalFrontier W ∪
          Gamma.terminalFrontier A.touchedReference ∧
      (imaginaryWeb Y kappa).vertexSet U =
        ((imaginaryWeb Y kappa).vertexSet W ∪ T.connector.support) ∪
          Gamma.vertexSet T.companions ∧
      ∀ r : Ray (imaginaryWeb Y kappa).graph, Sum.inr r ∈ U →
        ∃ r0 : Ray (imaginaryWeb Y kappa).graph, Sum.inr r0 ∈ W ∧
          r0.edgeSet \ {(s, t)} ⊆ r.edgeSet := by
  obtain ⟨U, hU, hUI, hUT, hUV, _hUE, htrace⟩ :=
    exists_weakSubdivision_with_companions_exact T hs ht hW hedge hconnector hcompanions
  exact ⟨U, hU, hUI, hUT, hUV, htrace⟩

/-- The exact boundary and carrier interface of the actual local union. -/
theorem exists_weakSubdivision_with_companions
    {Z : Set Gamma.DPath} {s t : V} {A : Occurrence Z s}
    (T : TouchedWeakSwitch A t)
    (hs : s ∉ Gamma.vertexSet Z) (ht : t ∉ Gamma.vertexSet Z)
    {W : Set (imaginaryWeb Y kappa).DPath}
    (hW : (imaginaryWeb Y kappa).IsWarp W)
    (hedge : (s, t) ∈ familyEdges W)
    (hconnector : T.connector.support ∩ (imaginaryWeb Y kappa).vertexSet W ⊆ {s, t})
    (hcompanions : Disjoint (Gamma.vertexSet T.companions)
      ((imaginaryWeb Y kappa).vertexSet W)) :
    ∃ U : Set (imaginaryWeb Y kappa).DPath,
      (imaginaryWeb Y kappa).IsWarp U ∧
      (imaginaryWeb Y kappa).initialSet U =
        (imaginaryWeb Y kappa).initialSet W ∪ Gamma.initialSet A.touchedReference ∧
      (imaginaryWeb Y kappa).terminalFrontier U =
        (imaginaryWeb Y kappa).terminalFrontier W ∪
          Gamma.terminalFrontier A.touchedReference ∧
      (imaginaryWeb Y kappa).vertexSet U =
        ((imaginaryWeb Y kappa).vertexSet W ∪ T.connector.support) ∪
          Gamma.vertexSet T.companions := by
  obtain ⟨U, hU, hUI, hUT, hUV, _htrace⟩ :=
    exists_weakSubdivision_with_companions_and_rayTrace T hs ht
      hW hedge hconnector hcompanions
  exact ⟨U, hU, hUI, hUT, hUV⟩

#print axioms exists_weakSubdivision_with_companions
#print axioms exists_weakSubdivision_with_companions_and_rayTrace
#print axioms exists_weakSubdivision_with_companions_exact

end Erdos599.Blueprint.ColouredSafeShortcutGraph
