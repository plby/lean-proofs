/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualColorOrder

/-!
# Finite localization of the designated colour

A marked one-hole route is finite even when the old designated linkage is
infinite.  Consequently it can meet only finitely many components of that
linkage.  This file makes the localization exact: after replacing the whole
designated family by the components which meet a route vertex, every marked
transition and every possible chord between route states is unchanged.

This is the finite reduction needed before applying a colour-sensitive
switch.  It is stronger than merely saying that the set of backward edges is
finite, because the ready/pending marking also tests membership in the whole
old carrier.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualTouchedPaths

open DWeb Alternating

universe u

variable {V : Type u}

/-- The vertices occurring as states of a finite marked route. -/
def routeVertexSet (l : List (OneHoleResidualState V)) : Set V :=
  Set.range fun i : Fin l.length => l[i].vertex

theorem routeVertexSet_finite (l : List (OneHoleResidualState V)) :
    (routeVertexSet l).Finite := by
  exact Set.finite_range _

theorem state_vertex_mem_routeVertexSet
    {l : List (OneHoleResidualState V)} {s : OneHoleResidualState V}
    (hs : s ∈ l) : s.vertex ∈ routeVertexSet l := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
  exact ⟨⟨i, hi⟩, rfl⟩

/-- Members of a path family which meet a specified vertex set. -/
def pathsMeetingVertices
    (G : DWeb V) (P : Set G.DPath) (S : Set V) : Set G.DPath :=
  {p | p ∈ P ∧ (p.support ∩ S).Nonempty}

@[simp]
theorem mem_pathsMeetingVertices
    {G : DWeb V} {P : Set G.DPath} {S : Set V} {p : G.DPath} :
    p ∈ pathsMeetingVertices G P S ↔
      p ∈ P ∧ (p.support ∩ S).Nonempty :=
  Iff.rfl

theorem pathsMeetingVertices_subset
    (G : DWeb V) (P : Set G.DPath) (S : Set V) :
    pathsMeetingVertices G P S ⊆ P := by
  exact fun _ hp ↦ hp.1

private theorem pathsThrough_finite
    {G : DWeb V} {P : Set G.DPath} (hP : G.IsWarp P) (x : V) :
    {p | p ∈ P ∧ x ∈ p.support}.Finite := by
  classical
  let F : Set G.DPath := {p | p ∈ P ∧ x ∈ p.support}
  by_cases hF : F.Nonempty
  · obtain ⟨p, hpF⟩ := hF
    apply (Set.finite_singleton p).subset
    intro q hqF
    have hpP : p ∈ P := hpF.1
    have hqP : q ∈ P := hqF.1
    have hqp : q = p := by
      by_contra hqp
      exact Set.disjoint_left.1 (hP hqP hpP hqp) hqF.2 hpF.2
    simpa only [Set.mem_singleton_iff] using hqp
  · change F.Finite
    rw [Set.not_nonempty_iff_eq_empty.mp hF]
    exact Set.finite_empty

/-- A disjoint path family has only finitely many components meeting a
finite vertex set. -/
theorem pathsMeetingVertices_finite_of_isWarp
    {G : DWeb V} {P : Set G.DPath} (hP : G.IsWarp P)
    {S : Set V} (hS : S.Finite) :
    (pathsMeetingVertices G P S).Finite := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      have hempty : pathsMeetingVertices G P ∅ = ∅ := by
        ext p
        simp [pathsMeetingVertices]
      rw [hempty]
      exact Set.finite_empty
  | @insert x S hx hS ih =>
      have hsub : pathsMeetingVertices G P (insert x S) ⊆
          {p | p ∈ P ∧ x ∈ p.support} ∪
            pathsMeetingVertices G P S := by
        intro p hp
        obtain ⟨hpP, y, hyp, hy⟩ := hp
        rcases hy with rfl | hyS
        · exact Or.inl ⟨hpP, hyp⟩
        · exact Or.inr ⟨hpP, y, hyp, hyS⟩
      exact ((pathsThrough_finite hP x).union ih).subset hsub

/-- The finite subfamily of designated paths which meet the marked route. -/
def touchedDesignatedPaths
    (G : DWeb V) (P : Set G.DPath)
    (l : List (OneHoleResidualState V)) : Set G.DPath :=
  pathsMeetingVertices G P (routeVertexSet l)

theorem touchedDesignatedPaths_finite
    {G : DWeb V} {P : Set G.DPath} (hP : G.IsWarp P)
    (l : List (OneHoleResidualState V)) :
    (touchedDesignatedPaths G P l).Finite := by
  exact pathsMeetingVertices_finite_of_isWarp hP (routeVertexSet_finite l)

theorem touchedDesignatedPaths_subset
    (G : DWeb V) (P : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    touchedDesignatedPaths G P l ⊆ P :=
  pathsMeetingVertices_subset G P (routeVertexSet l)

/-- On a route vertex, membership in the full designated carrier is exactly
membership in the carrier of the finite touched subfamily. -/
theorem route_vertex_mem_vertexSet_touched_iff
    {G : DWeb V} {P : Set G.DPath}
    {l : List (OneHoleResidualState V)} {x : V}
    (hx : x ∈ routeVertexSet l) :
    x ∈ G.vertexSet P ↔
      x ∈ G.vertexSet (touchedDesignatedPaths G P l) := by
  constructor
  · rintro ⟨p, hpP, hxp⟩
    exact ⟨p, ⟨hpP, x, hxp, hx⟩, hxp⟩
  · rintro ⟨p, hpT, hxp⟩
    exact ⟨p, (touchedDesignatedPaths_subset G P l hpT), hxp⟩

/-- Every designated edge whose left endpoint is a route vertex already
belongs to a touched designated component. -/
theorem familyEdge_mem_touched_of_left_route_vertex
    {G : DWeb V} {P : Set G.DPath}
    {l : List (OneHoleResidualState V)} {x y : V}
    (hx : x ∈ routeVertexSet l) (hxy : (x, y) ∈ familyEdges P) :
    (x, y) ∈ familyEdges (touchedDesignatedPaths G P l) := by
  simp only [familyEdges, Set.mem_iUnion] at hxy ⊢
  obtain ⟨p, hpP, he⟩ := hxy
  have hxp : x ∈ p.support := (p.edgeSet_subset_support_prod he).1
  exact ⟨p, ⟨hpP, x, hxp, hx⟩, he⟩

/-- Along route vertices, the full and localized designated edge relations
coincide. -/
theorem familyEdge_touched_iff_of_left_route_vertex
    {G : DWeb V} {P : Set G.DPath}
    {l : List (OneHoleResidualState V)} {x y : V}
    (hx : x ∈ routeVertexSet l) :
    (x, y) ∈ familyEdges P ↔
      (x, y) ∈ familyEdges (touchedDesignatedPaths G P l) := by
  constructor
  · exact familyEdge_mem_touched_of_left_route_vertex hx
  · intro hxy
    simp only [familyEdges, Set.mem_iUnion] at hxy ⊢
    obtain ⟨p, hpT, he⟩ := hxy
    exact ⟨p, touchedDesignatedPaths_subset G P l hpT, he⟩

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

private theorem markedStep_localize_designated_iff
    {G : DWeb V} {P L : Set G.DPath}
    {l : List (OneHoleResidualState V)}
    {s t : OneHoleResidualState V}
    (hs : s ∈ l) (ht : t ∈ l) :
    G.OneHoleMarkedStep (P ∪ L) s t ↔
      G.OneHoleMarkedStep (touchedDesignatedPaths G P l ∪ L) s t := by
  have hsRoute : s.vertex ∈ routeVertexSet l :=
    state_vertex_mem_routeVertexSet hs
  have htRoute : t.vertex ∈ routeVertexSet l :=
    state_vertex_mem_routeVertexSet ht
  have hst := familyEdge_touched_iff_of_left_route_vertex
    (P := P) (l := l) hsRoute (y := t.vertex)
  have hts := familyEdge_touched_iff_of_left_route_vertex
    (P := P) (l := l) htRoute (y := s.vertex)
  have htCarrier := route_vertex_mem_vertexSet_touched_iff
    (G := G) (P := P) htRoute
  cases s <;> cases t <;>
    simp only [OneHoleResidualState.vertex_ready,
      OneHoleResidualState.vertex_pending] at hst hts htCarrier <;>
    simp only [OneHoleMarkedStep, familyEdges_union,
      G.vertexSet_union, Set.mem_union] <;>
    tauto

/-- Replacing an arbitrary designated family by the finitely many components
which meet the route preserves the entire reduced marked route, including
chordlessness. -/
theorem reducedRoute_localize_designated
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l) :
    IsReducedMarkedRoute G
      (touchedDesignatedPaths G P l ∪ L) a b l := by
  refine ⟨⟨hl.1.1, ?_, hl.1.2.2⟩, hl.2.1, ?_⟩
  · apply hl.1.2.1.imp_of_mem_imp
    intro s t hs ht hst
    exact (markedStep_localize_designated_iff hs ht).mp hst
  · intro pre mid post s t hdecomp hmid hst
    apply hl.2.2 pre mid post s t hdecomp hmid
    have hs : s ∈ l := by rw [hdecomp]; simp
    have ht : t ∈ l := by rw [hdecomp]; simp
    exact (markedStep_localize_designated_iff hs ht).mpr hst

/-- Every designated backward edge of the route is owned by the finite
touched subfamily. -/
theorem designated_backwardEdges_subset_familyEdges_touched
    (G : DWeb V) (P L : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    oneHoleRouteBackwardEdges G (P ∪ L) l ∩ familyEdges P ⊆
      familyEdges (touchedDesignatedPaths G P l) := by
  rintro e ⟨⟨i, hi, rfl⟩, heP⟩
  apply familyEdge_mem_touched_of_left_route_vertex
    (hxy := heP)
  apply state_vertex_mem_routeVertexSet
  exact List.getElem_mem (show i.1 + 1 < l.length by omega)

#print axioms routeVertexSet_finite
#print axioms pathsMeetingVertices_finite_of_isWarp
#print axioms touchedDesignatedPaths_finite
#print axioms route_vertex_mem_vertexSet_touched_iff
#print axioms familyEdge_touched_iff_of_left_route_vertex
#print axioms reducedRoute_localize_designated
#print axioms designated_backwardEdges_subset_familyEdges_touched

end SingularMarkedResidualTouchedPaths
end CardinalInduction
end Erdos599
