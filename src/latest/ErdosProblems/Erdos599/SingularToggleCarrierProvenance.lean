/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularToggleExactRelation
import ErdosProblems.Erdos599.SingularMarkedResidualTouchedPaths
import ErdosProblems.Erdos599.AlternatingComponents

/-!
# Provenance of vertices discarded by a finite marked toggle

The path part of the locally bi-unique toggled relation can omit an old
carrier vertex for only two reasons.  Either an old incident edge was
cancelled by a backward step of the marked route, in which case the vertex
is a route vertex, or a surviving incident edge belongs to a directed-cycle
component discarded from the cyclowarp path part.

This is the precise structural information retained by the exact-relation
strengthening of the finite exchange.  Endpoint equations alone do not
distinguish these two cases.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularToggleCarrierProvenance

open DWeb Alternating
open SingularMarkedResidualTouchedPaths

universe u

variable {V : Type u}

/-- Every non-root vertex of an alternating component is carried by one of
the two path families.  The root is excluded because components are defined
reflexively even when the root is outside both carriers. -/
theorem mem_vertexSet_union_of_mem_component_of_ne
    {G : DWeb V} {W Y : Set G.DPath} {root x : V}
    (hx : x ∈ AlternatingComponents.component W Y root)
    (hxr : x ≠ root) :
    x ∈ G.vertexSet W ∪ G.vertexSet Y := by
  rcases Relation.ReflTransGen.cases_tail hx with hEq | ⟨z, _hz, hzx⟩
  · exact False.elim (hxr hEq)
  · rcases hzx with hforward | hbackward
    · rcases hforward with hW | hY
      · simp only [familyEdges, Set.mem_iUnion] at hW
        obtain ⟨p, hpW, hpedge⟩ := hW
        exact Or.inl ⟨p, hpW, (p.edgeSet_subset_support_prod hpedge).2⟩
      · simp only [familyEdges, Set.mem_iUnion] at hY
        obtain ⟨p, hpY, hpedge⟩ := hY
        exact Or.inr ⟨p, hpY, (p.edgeSet_subset_support_prod hpedge).2⟩
    · rcases hbackward with hW | hY
      · simp only [familyEdges, Set.mem_iUnion] at hW
        obtain ⟨p, hpW, hpedge⟩ := hW
        exact Or.inl ⟨p, hpW, (p.edgeSet_subset_support_prod hpedge).1⟩
      · simp only [familyEdges, Set.mem_iUnion] at hY
        obtain ⟨p, hpY, hpedge⟩ := hY
        exact Or.inr ⟨p, hpY, (p.edgeSet_subset_support_prod hpedge).1⟩

/-- An old carrier vertex absent from the path part of the exact marked
toggle is either visited by the marked route or lies on one of the discarded
directed cycles. -/
theorem mem_routeVertexSet_or_discardedCycle
    {G : DWeb V} {J : Set G.DPath} {a b x : V}
    {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (hl : IsReducedMarkedRoute G J a b l)
    (C : Cyclowarp G)
    (hCedges : C.edges = oneHoleRouteToggledEdges G J l)
    (hCisolated : C.isolated = isolatedVertices J)
    (hxJ : x ∈ G.vertexSet J)
    (hxNotPath : x ∉ G.vertexSet C.pathPart) :
    x ∈ routeVertexSet l ∨
      ∃ c ∈ C.cycles, x ∈ c.support := by
  have hxNotIsolated : x ∉ isolatedVertices J := by
    intro hxIso
    have hxCIso : x ∈ C.isolated := by
      rw [hCisolated]
      exact hxIso
    exact hxNotPath (isolatedVertices_subset_vertexSet C.pathPart hxCIso)
  have hxIncident :
      HasIncoming (familyEdges J) x ∨ HasOutgoing (familyEdges J) x := by
    rw [vertexSet_eq_isolated_union_incident hJ.hasFiniteCharacter] at hxJ
    exact hxJ.resolve_left hxNotIsolated
  have classifyIncident : ∀ {u v : V},
      (u, v) ∈ familyEdges J → (x = u ∨ x = v) →
        x ∈ routeVertexSet l ∨
          ∃ c ∈ C.cycles, x ∈ c.support := by
    intro u v huv hxuv
    by_cases htoggle :
        (u, v) ∈ oneHoleRouteToggledEdges G J l
    · have hCedge : (u, v) ∈ C.edges := by
        rw [hCedges]
        exact htoggle
      rcases hCedge with hpath | hcycle
      · simp only [familyEdges, Set.mem_iUnion] at hpath
        obtain ⟨p, hpC, hpedge⟩ := hpath
        have hends := p.edgeSet_subset_support_prod hpedge
        exfalso
        apply hxNotPath
        refine ⟨p, hpC, ?_⟩
        rcases hxuv with rfl | rfl
        · exact hends.1
        · exact hends.2
      · simp only [Set.mem_iUnion] at hcycle
        obtain ⟨c, hcC, hcedge⟩ := hcycle
        obtain ⟨i, hi⟩ := hcedge
        have hpair : (u, v) = (c.vertex i, c.vertex (c.next i)) := hi
        have hu : u = c.vertex i := congrArg Prod.fst hpair
        have hv : v = c.vertex (c.next i) := congrArg Prod.snd hpair
        right
        refine ⟨c, hcC, ?_⟩
        rcases hxuv with rfl | rfl
        · rw [hu]
          exact ⟨i, rfl⟩
        · rw [hv]
          exact ⟨c.next i, rfl⟩
    · have hbackward :
          (u, v) ∈ oneHoleRouteBackwardEdges G J l := by
        by_contra hnotBackward
        apply htoggle
        exact Or.inl ⟨huv, hnotBackward⟩
      obtain ⟨i, _hi, hpair⟩ := hbackward
      have hu : u = (oneHoleRouteTarget l i).vertex :=
        congrArg Prod.fst hpair
      have hv : v = (oneHoleRouteSource l i).vertex :=
        congrArg Prod.snd hpair
      left
      rcases hxuv with rfl | rfl
      · rw [hu]
        refine ⟨⟨i.1 + 1, ?_⟩, rfl⟩
        have hiLt := i.isLt
        omega
      · rw [hv]
        refine ⟨⟨i.1, ?_⟩, rfl⟩
        have hiLt := i.isLt
        omega
  rcases hxIncident with ⟨y, hyx⟩ | ⟨y, hxy⟩
  · exact classifyIncident hyx (Or.inr rfl)
  · exact classifyIncident hxy (Or.inl rfl)

#print axioms mem_vertexSet_union_of_mem_component_of_ne
#print axioms mem_routeVertexSet_or_discardedCycle

end SingularToggleCarrierProvenance
end CardinalInduction
end Erdos599
