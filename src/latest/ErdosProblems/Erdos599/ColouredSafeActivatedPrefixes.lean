/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointBlueprint
import ErdosProblems.Erdos599.ColouredSafeGraphLift
import ErdosProblems.Erdos599.MarkedRayFiniteEdgeStability

/-!
# Activated original-source prefixes with an explicit old carrier

These are finite ladder-reference prefixes, not full limiting owners (which
may be rays). They are disjoint from the old carrier and lie in the closing
set. Their unchanged initials supply source coverage after the frontier moves.
-/

namespace Erdos599.Blueprint.ColouredSafeActivatedPrefixes

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open DWeb.KappaLadder.Deferred ColouredSafeGraphLift

universe u

variable {V : Type u} {Gamma D : DWeb V} {rho : Cardinal.{u}}

def prefixes (L : Gamma.KappaLadder rho) (a : Stage rho)
    (oldCarrier X : Set V) : Set Gamma.DPath :=
  {q | q ∈ ladderReference L a ∧ q.initial ∈ Gamma.source ∧
    Disjoint q.support oldCarrier ∧ (q.support ∩ X).Nonempty}

variable {L : Gamma.KappaLadder rho} {a b : Stage rho} {oldCarrier X : Set V}

theorem isWarp (hL : HalfwayGeometry L) : Gamma.IsWarp (prefixes L a oldCarrier X) :=
  (ladderReference.isWarp hL).subset (fun _ hp ↦ hp.1)

theorem finiteCharacter : Gamma.HasFiniteCharacter (prefixes L a oldCarrier X) := by
  intro p hp
  exact ladderReference.finiteCharacter hp.1

theorem vertices_roofed (hL : HalfwayGeometry L) :
    Gamma.vertexSet (prefixes L a oldCarrier X) ⊆ Gamma.roof (L.frontier a) := by
  rintro x ⟨q, hq, hxq⟩
  exact ladderReference.vertexSet_subset_roof hL
    (vertexSet_warpAt_subset_roof_terminalFrontier hL a) ⟨q, hq.1, hxq⟩

theorem terminals_subset (hL : HalfwayGeometry L) :
    Gamma.terminalFrontier (prefixes L a oldCarrier X) ⊆ L.frontier a := by
  rintro x ⟨q, hq, hqx⟩
  rw [← ladderReference.terminalFrontier_eq hL]
  exact ⟨q, hq.1, hqx⟩

theorem vertices_disjoint :
    Disjoint (Gamma.vertexSet (prefixes L a oldCarrier X)) oldCarrier := by
  apply Set.disjoint_left.mpr
  rintro x ⟨q, hq, hxq⟩ hxOld
  exact Set.disjoint_left.mp hq.2.2.1 hxq hxOld

theorem support_subset_closed (hL : HalfwayGeometry L)
    (hclosed : ClosedUnderPaths Gamma L.limitWarp X)
    {q : Gamma.DPath} (hq : q ∈ prefixes L a oldCarrier X) : q.support ⊆ X := by
  let qs : ladderReference L a := ⟨q, hq.1⟩
  have hp := ladderReference.limitExtension_mem hL qs
  have hqp := ladderReference.extends_limitExtension hL qs
  obtain ⟨x, hxq, hxX⟩ := hq.2.2.2
  exact (Gamma.support_mono_of_extends hqp).trans
    (hclosed _ hp ⟨x, Gamma.support_mono_of_extends hqp hxq, hxX⟩)

theorem vertices_subset_closed (hL : HalfwayGeometry L)
    (hclosed : ClosedUnderPaths Gamma L.limitWarp X) :
    Gamma.vertexSet (prefixes L a oldCarrier X) ⊆ X := by
  rintro x ⟨q, hq, hxq⟩
  exact support_subset_closed hL hclosed hq hxq

/-- The original owner has an activated prefix with exactly the same root. -/
theorem initial_mem_of_owner_meets (hL : HalfwayGeometry L)
    (hclosed : ClosedUnderPaths Gamma L.limitWarp X)
    {p : Gamma.DPath}
    (hp : p ∈ referencePathsMeeting L.limitWarp (L.frontier a) \
      referencePathsMeeting L.limitWarp oldCarrier)
    (hsource : p.initial ∈ Gamma.source) (hmeet : (p.support ∩ X).Nonempty) :
    p.initial ∈ Gamma.initialSet (prefixes L a oldCarrier X) := by
  obtain ⟨t, htp, ht⟩ := hp.1.2
  obtain ⟨q, hq, _hqt, hqp⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit hL hp.1.1 ht htp
  have hqX : q.support ⊆ X :=
    (Gamma.support_mono_of_extends hqp).trans (hclosed p hp.1.1 hmeet)
  refine ⟨q, ⟨hq, ?_, ?_, ?_⟩, Gamma.extends_initial hqp⟩
  · exact (Gamma.extends_initial hqp).symm ▸ hsource
  · apply Set.disjoint_left.mpr
    intro x hxq hxOld
    exact hp.2 ⟨hp.1.1, x, Gamma.support_mono_of_extends hqp hxq, hxOld⟩
  · exact ⟨q.initial, q.initial_mem_support, hqX q.initial_mem_support⟩

/-- Retained old roots and activated prefix roots prove the exact source
condition at the later frontier. Lost owners are explicitly registered. -/
theorem source_coverage (hL : HalfwayGeometry L)
    (hclosed : ClosedUnderPaths Gamma L.limitWarp X) {W U : Set D.DPath}
    (hcover : Gamma.source ⊆ D.initialSet W ∪ Gamma.initialSet
      (referencePathsMeeting L.limitWarp (L.frontier a) \
        referencePathsMeeting L.limitWarp (D.vertexSet W)))
    (hI : D.initialSet W ⊆ D.initialSet U)
    (hP : Gamma.initialSet (prefixes L a (D.vertexSet W) X) ⊆ D.initialSet U)
    (hV : D.vertexSet U ⊆ D.vertexSet W ∪ X)
    (hlost : referencePathsMeeting L.limitWarp (L.frontier a) \
      referencePathsMeeting L.limitWarp (L.frontier b) ⊆ referencePathsMeeting L.limitWarp X) :
    Gamma.source ⊆ D.initialSet U ∪ Gamma.initialSet
      (referencePathsMeeting L.limitWarp (L.frontier b) \
        referencePathsMeeting L.limitWarp (D.vertexSet U)) := by
  intro x hx
  rcases hcover hx with hxW | ⟨p, hp, hpx⟩
  · exact Or.inl (hI hxW)
  · have hroot (hpX : (p.support ∩ X).Nonempty) : x ∈ D.initialSet U := by
      rw [← hpx]
      exact hP (initial_mem_of_owner_meets hL hclosed hp (hpx.symm ▸ hx) hpX)
    by_cases hpU : p ∈ referencePathsMeeting L.limitWarp (D.vertexSet U)
    · left
      apply hroot
      obtain ⟨v, hvp, hvU⟩ := hpU.2
      rcases hV hvU with hvW | hvX
      · exact False.elim (hp.2 ⟨hp.1.1, v, hvp, hvW⟩)
      · exact ⟨v, hvp, hvX⟩
    · by_cases hpB : p ∈ referencePathsMeeting L.limitWarp (L.frontier b)
      · exact Or.inr ⟨p, ⟨hpB, hpU⟩, hpx⟩
      · exact Or.inl (hroot (hlost ⟨hp.1, hpB⟩).2)

/-- A concrete disjoint union with the lifted finite activated prefixes. -/
def seedFamily (L : Gamma.KappaLadder rho) (a : Stage rho)
    (hAdj : ∀ {x y}, Gamma.graph.Adj x y → D.graph.Adj x y)
    (W : Set D.DPath) (X : Set V) : Set D.DPath :=
  W ∪ liftFamily hAdj (prefixes L a (D.vertexSet W) X)

variable (hAdj : ∀ {x y}, Gamma.graph.Adj x y → D.graph.Adj x y)
variable {W : Set D.DPath}

@[simp] theorem seedFamily_vertices :
    D.vertexSet (seedFamily L a hAdj W X) =
      D.vertexSet W ∪ Gamma.vertexSet (prefixes L a (D.vertexSet W) X) := by
  rw [seedFamily, D.vertexSet_union, liftFamily_vertexSet]

@[simp] theorem seedFamily_initials :
    D.initialSet (seedFamily L a hAdj W X) =
      D.initialSet W ∪ Gamma.initialSet (prefixes L a (D.vertexSet W) X) := by
  rw [seedFamily, D.initialSet_union, liftFamily_initialSet]

@[simp] theorem seedFamily_terminals :
    D.terminalFrontier (seedFamily L a hAdj W X) =
      D.terminalFrontier W ∪ Gamma.terminalFrontier (prefixes L a (D.vertexSet W) X) := by
  rw [seedFamily, D.terminalFrontier_union, liftFamily_terminalFrontier]

@[simp] theorem seedFamily_edges :
    familyEdges (seedFamily L a hAdj W X) =
      familyEdges W ∪ familyEdges (prefixes L a (D.vertexSet W) X) := by
  rw [seedFamily, RelationDecomposition.DWeb.familyEdges_union_local, liftFamily_edges]

theorem seedFamily_isWarp (hL : HalfwayGeometry L) (hW : D.IsWarp W) :
    D.IsWarp (seedFamily L a hAdj W X) := by
  have hP := liftFamily_isWarp hAdj
    (isWarp (a := a) (oldCarrier := D.vertexSet W) (X := X) hL)
  have hcross : Disjoint
      (D.vertexSet (liftFamily hAdj (prefixes L a (D.vertexSet W) X))) (D.vertexSet W) := by
    rw [liftFamily_vertexSet]
    exact vertices_disjoint
  intro p hp q hq hpq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact hW hp hq hpq
  · apply Set.disjoint_left.mpr
    intro x hxp hxq
    exact Set.disjoint_left.mp hcross ⟨q, hq, hxq⟩ ⟨p, hp, hxp⟩
  · apply Set.disjoint_left.mpr
    intro x hxp hxq
    exact Set.disjoint_left.mp hcross ⟨p, hp, hxp⟩ ⟨q, hq, hxq⟩
  · exact hP hp hq hpq

theorem seedFamily_marked {marked : V → V → Prop}
    (hmarked : D.InfinitelyManyMarkedEdges W marked) :
    D.InfinitelyManyMarkedEdges (seedFamily L a hAdj W X) marked :=
  DWeb.infinitelyManyMarkedEdges_union_finiteCharacter hmarked
    (liftFamily_finiteCharacter hAdj finiteCharacter)

#print axioms support_subset_closed
#print axioms source_coverage
#print axioms seedFamily_isWarp
#print axioms seedFamily_marked

end Erdos599.Blueprint.ColouredSafeActivatedPrefixes
