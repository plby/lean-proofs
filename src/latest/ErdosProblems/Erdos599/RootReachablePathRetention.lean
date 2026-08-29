/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RootReachableRelation
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# Root-reachable restriction retains old finite paths and rays

Each vertex of a directed path has a finite prefix, including when the path
is a ray. Thus a family whose initial vertices are reachable survives the
root-reachable restriction in its entirety.
-/

noncomputable section

open Set

namespace Erdos599.RootReachableRelation

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}
variable (E : Set (V × V)) (R : Set V)

theorem path_initial_reaches_of_mem_support
    (p : Gamma.DPath) (hp : p.edgeSet ⊆ E)
    {x : V} (hx : x ∈ p.support) :
    Relation.ReflTransGen (fun a b ↦ (a, b) ∈ E) p.initial x := by
  rcases p with p | r
  · exact GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      p hp hx
  · obtain ⟨n, rfl⟩ := hx
    have hreach : ∀ n, Relation.ReflTransGen
        (fun a b ↦ (a, b) ∈ E) (r 0) (r n) := by
      intro n
      induction n with
      | zero => exact .refl
      | succ n ih => exact ih.tail (hp ⟨n, rfl⟩)
    exact hreach n

theorem path_support_subset_carrier
    (p : Gamma.DPath) (hp : p.edgeSet ⊆ E)
    (hstart : p.initial ∈ carrier E R) : p.support ⊆ carrier E R := by
  intro x hx
  exact carrier_of_reflTransGen_of_mem E R hstart
    (path_initial_reaches_of_mem_support E p hp hx)

theorem path_edgeSet_subset_edges
    (p : Gamma.DPath) (hp : p.edgeSet ⊆ E)
    (hstart : p.initial ∈ carrier E R) : p.edgeSet ⊆ edges E R := by
  intro e he
  exact ⟨hp he, path_support_subset_carrier E R p hp hstart
    (p.edgeSet_subset_support_prod he).1⟩

theorem family_vertices_retained
    (W : Set Gamma.DPath) (hWedges : familyEdges W ⊆ E)
    (hWinitial : Gamma.initialSet W ⊆ carrier E R) :
    Gamma.vertexSet W ⊆ carrier E R := by
  rintro x ⟨p, hp, hxp⟩
  apply path_support_subset_carrier E R p _ (hWinitial ⟨p, hp, rfl⟩) hxp
  intro e he
  exact hWedges (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, he⟩⟩)

theorem family_edges_retained
    (W : Set Gamma.DPath) (hWedges : familyEdges W ⊆ E)
    (hWinitial : Gamma.initialSet W ⊆ carrier E R) :
    familyEdges W ⊆ edges E R := by
  intro e he
  exact ⟨hWedges he, family_vertices_retained E R W hWedges hWinitial
    (familyEdges_subset_vertexSet_prod W he).1⟩

#print axioms path_support_subset_carrier
#print axioms family_edges_retained

end Erdos599.RootReachableRelation
