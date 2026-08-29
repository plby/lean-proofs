/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeWeakSubdivision

/-!
# Predicate-parametric ray marks under finite edge changes

The edge-index map of a ray is injective. Consequently finitely many lost
edges cannot destroy infinitely many marked edges. This argument does not
identify native occurrence marks with legacy alternating-path marks.
-/

noncomputable section

namespace Erdos599.DirectedPath.Ray

open Set

universe u

variable {V : Type u} {D E : Digraph V}

theorem markedIndices_infinite_of_cofinite_edges
    (marked : V → V → Prop) (r : Ray D) (r' : Ray E)
    (hmarked : {n : ℕ | marked (r n) (r (n + 1))}.Infinite)
    {lost : Set (V × V)} (hlost : lost.Finite)
    (hretain : r.edgeSet \ lost ⊆ r'.edgeSet) :
    {n : ℕ | marked (r' n) (r' (n + 1))}.Infinite := by
  let edges : Set (V × V) :=
    (fun n : ℕ ↦ (r n, r (n + 1))) '' {n | marked (r n) (r (n + 1))}
  have hinfinite : edges.Infinite := hmarked.image (by
    intro n _ m _ he
    exact r.injective (congrArg Prod.fst he))
  have hremain : (edges \ lost).Infinite := hinfinite.sdiff hlost
  have hsubset : edges \ lost ⊆
      (fun n : ℕ ↦ (r' n, r' (n + 1))) ''
        {n | marked (r' n) (r' (n + 1))} := by
    rintro e ⟨⟨n, hn, rfl⟩, hnot⟩
    obtain ⟨m, hm⟩ := hretain ⟨⟨n, rfl⟩, hnot⟩
    refine ⟨m, ?_, hm.symm⟩
    change marked (r' m) (r' (m + 1))
    have hfirst : r n = r' m := congrArg Prod.fst hm
    have hlast : r (n + 1) = r' (m + 1) := congrArg Prod.snd hm
    rw [← hfirst, ← hlast]
    exact hn
  by_contra hfinite
  exact hremain (((Set.not_infinite.mp hfinite).image _).subset hsubset)

#print axioms markedIndices_infinite_of_cofinite_edges

end Erdos599.DirectedPath.Ray

namespace Erdos599.DWeb

open Set _root_.Erdos599.DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

def InfinitelyManyMarkedEdges (W : Set Gamma.DPath) (marked : V → V → Prop) : Prop :=
  ∀ r : Ray Gamma.graph, Sum.inr r ∈ W →
    {n : ℕ | marked (r n) (r (n + 1))}.Infinite

theorem infinitelyManyMarkedEdges_of_rayTrace
    {W U : Set Gamma.DPath} {marked : V → V → Prop}
    (hmarked : Gamma.InfinitelyManyMarkedEdges W marked)
    {lost : Set (V × V)} (hlost : lost.Finite)
    (htrace : ∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
      ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧ r0.edgeSet \ lost ⊆ r.edgeSet) :
    Gamma.InfinitelyManyMarkedEdges U marked := by
  intro r hr
  obtain ⟨r0, hr0, hretain⟩ := htrace r hr
  exact r0.markedIndices_infinite_of_cofinite_edges marked r (hmarked r0 hr0) hlost hretain

theorem infinitelyManyMarkedEdges_union_finiteCharacter
    {W K : Set Gamma.DPath} {marked : V → V → Prop}
    (hmarked : Gamma.InfinitelyManyMarkedEdges W marked)
    (hfinite : Gamma.HasFiniteCharacter K) :
    Gamma.InfinitelyManyMarkedEdges (W ∪ K) marked := by
  intro r hr
  rcases hr with hr | hr
  · exact hmarked r hr
  · obtain ⟨p, hp⟩ := hfinite hr
    cases hp

/-- The finite lost set may depend on the new ray, as when only a suffix
of its old owner survives a two-port splice. -/
theorem infinitelyManyMarkedEdges_of_finite_rayTrace
    {W U : Set Gamma.DPath} {marked : V → V → Prop}
    (hmarked : Gamma.InfinitelyManyMarkedEdges W marked)
    (htrace : ∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
      ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
        ∃ lost : Set (V × V), lost.Finite ∧ r0.edgeSet \ lost ⊆ r.edgeSet) :
    Gamma.InfinitelyManyMarkedEdges U marked := by
  intro r hr
  obtain ⟨r0, hr0, lost, hlost, hretain⟩ := htrace r hr
  exact r0.markedIndices_infinite_of_cofinite_edges marked r (hmarked r0 hr0) hlost hretain

#print axioms infinitelyManyMarkedEdges_of_rayTrace
#print axioms infinitelyManyMarkedEdges_union_finiteCharacter
#print axioms infinitelyManyMarkedEdges_of_finite_rayTrace

end Erdos599.DWeb
