/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Ray-compatible relation decomposition

A locally bi-unique directed relation with no directed cycle and no
reverse-directed ray decomposes into finite paths and forward rays.  This
is the exact infinite analogue of the finite-character switching assembly
needed by the simultaneous grounding construction.
-/

noncomputable section

namespace Erdos599
namespace Alternating
namespace RayCompatibleRelationDecomposition

open Set DirectedPath RelationDecomposition

universe u

variable {V : Type u}

/-- Add prescribed singleton components to a forward-orbit decomposition. -/
theorem exists_warp_realizing_orientation_with_isolated
    (G : Erdos599.DWeb V) (E : Set (V × V)) (I : Set V)
    (O : ForwardOrientation G.graph)
    (hOE : O.edge = E)
    (hcarrier : O.carrier = IncidentVertices O.edge)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ W : Set G.DPath,
      G.IsWarp W ∧ familyEdges W = E ∧ isolatedVertices W = I := by
  let P : Set G.DPath := O.rootPaths
  let T : Set G.DPath := RelationDecomposition.DWeb.isolatedPaths G I
  have hPwarp : G.IsWarp P := O.rootPaths_pairwiseDisjoint
  have hPE : familyEdges P = E := by
    change O.rootPathEdges = E
    rw [O.rootPathEdges_eq, hOE]
  have hcross : ∀ p ∈ P, ∀ q ∈ T, Disjoint p.support q.support := by
    intro p hp q hq
    rcases hp with ⟨r, rfl⟩
    rcases hq with ⟨x, hxI, rfl⟩
    rw [G.support_trivialPath, Set.disjoint_singleton_right]
    intro hxr
    have hxcarrier : x ∈ O.carrier := O.rootPath_support_subset_carrier r hxr
    rw [hcarrier] at hxcarrier
    rcases hxcarrier with ⟨y, hxy | hyx⟩
    · exact (hI x hxI y).1 (hOE ▸ hxy)
    · exact (hI x hxI y).2 (hOE ▸ hyx)
  refine ⟨P ∪ T, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact hPwarp hp hq hpq
    · exact hcross p hp q hq
    · exact (hcross q hq p hp).symm
    · exact RelationDecomposition.DWeb.isolatedPaths_isWarp G I hp hq hpq
  · rw [RelationDecomposition.DWeb.familyEdges_union_local, hPE,
      RelationDecomposition.DWeb.familyEdges_isolatedPaths G I,
      Set.union_empty]
  · ext x
    simp only [isolatedVertices, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hx
      rcases hx with hx | hx
      · have hnone : x ∈ (∅ : Set V) := by
          rw [← RelationDecomposition.DWeb.rootPaths_no_isolated G O hcarrier]
          exact hx
        exact hnone.elim
      · exact (Set.ext_iff.mp
          (RelationDecomposition.DWeb.isolatedVertices_isolatedPaths G I) x).mp hx
    · intro hx
      exact Or.inr
        ((Set.ext_iff.mp
          (RelationDecomposition.DWeb.isolatedVertices_isolatedPaths G I) x).mpr hx)

/-- A bi-unique acyclic relation with no reverse ray is realized by a warp;
forward rays are retained as ray components. -/
theorem exists_warp_realizing_biUnique_with_isolated
    (G : Erdos599.DWeb V) (E : Set (V × V)) (I : Set V)
    (hgraph : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hcycle : ¬ ContainsDirectedCycle E)
    (hReverseRay : ¬ ContainsReverseDirectedRay E)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ W : Set G.DPath,
      G.IsWarp W ∧ familyEdges W = E ∧ isolatedVertices W = I := by
  let carrier := IncidentVertices E
  have hendpoints : ∀ e ∈ E, e.1 ∈ carrier ∧ e.2 ∈ carrier := by
    rintro ⟨x, y⟩ hxy
    exact ⟨incident_of_edge_left hxy, incident_of_edge_right hxy⟩
  let hwf : WellFounded (fun x y ↦ (x, y) ∈ E) :=
    ForwardOrientation.predecessor_wellFounded E hcycle hReverseRay
  let O : ForwardOrientation G.graph :=
    { edge := E
      carrier := carrier
      depth := ForwardOrientation.wellFoundedDepth E hwf
      component := ForwardOrientation.wellFoundedRoot E hwf
      edge_in_graph := hgraph
      endpoints_mem := hendpoints
      out_unique := fun hxy hxz ↦ hunique.2 hxy hxz
      in_unique := fun hxz hyz ↦ hunique.1 hxz hyz
      depth_step := fun hxy ↦
        ForwardOrientation.wellFoundedDepth_step E hunique hwf hxy
      component_step := fun hxy ↦
        ForwardOrientation.wellFoundedRoot_step E hunique hwf hxy
      root_label := fun _hx hdepth ↦
        ForwardOrientation.wellFoundedRoot_eq_self_of_depth_eq_zero E hwf hdepth
      predecessor := by
        intro x _hx hpos
        have hne : ForwardOrientation.wellFoundedDepth E hwf x ≠ 0 :=
          Nat.ne_of_gt hpos
        exact Classical.byContradiction fun hnot ↦
          hne ((ForwardOrientation.wellFoundedDepth_eq_zero_iff E hwf x).mpr hnot) }
  exact exists_warp_realizing_orientation_with_isolated G E I O rfl rfl hI

end RayCompatibleRelationDecomposition
end Alternating
end Erdos599
