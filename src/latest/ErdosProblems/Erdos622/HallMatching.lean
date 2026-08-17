/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib

/-!
# Hall and maximal-matching lemmas for Erdős Problem 622

This file collects finite deterministic facts about minimum vertex covers and
matchings.  The main Hall lemma applies to an independent minimum vertex cover,
which is exactly the situation in which the graph is bipartite with the cover
as one side.  The independence assumption is essential: two vertices of a
triangle form a minimum vertex cover but cannot both be matched outside it.
-/

open Function
open scoped SimpleGraph

namespace Erdos622

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Neighbors of `v` outside the finite vertex set `C`. -/
def outsideNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (v : V) : Finset V :=
  G.neighborFinset v \ C

@[simp]
theorem mem_outsideNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Finset V} {v w : V} :
    w ∈ outsideNeighborFinset G C v ↔ G.Adj v w ∧ w ∉ C := by
  simp [outsideNeighborFinset]

omit [Fintype V] [DecidableEq V] in
/-- An independent vertex cover gives a bipartition into the cover and its
complement. -/
theorem isBipartiteWith_of_isIndepSet_isVertexCover (G : SimpleGraph V)
    {C : Set V} (hI : G.IsIndepSet C) (hC : G.IsVertexCover C) :
    G.IsBipartiteWith C Cᶜ := by
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro v hvC hvCcompl
    exact hvCcompl hvC
  intro v w hvw
  rcases hC hvw with hvC | hwC
  · left
    refine ⟨hvC, ?_⟩
    intro hwC
    exact hI hvC hwC hvw.ne hvw
  · right
    refine ⟨?_, hwC⟩
    intro hvC
    exact hI hvC hwC hvw.ne hvw

/-- Replacing a subset `S` of an independent vertex cover by all of its
neighbors outside the cover still gives a vertex cover. -/
theorem vertexCover_replace_by_outsideNeighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C S : Finset V}
    (hI : G.IsIndepSet (C : Set V))
    (hC : G.IsVertexCover (C : Set V)) :
    G.IsVertexCover
      (↑((C \ S) ∪ S.biUnion (outsideNeighborFinset G C)) : Set V) := by
  intro v w hvw
  rcases hC hvw with hvC | hwC
  · by_cases hvS : v ∈ S
    · right
      have hwC' : w ∉ C := by
        intro hwC
        exact hI hvC hwC hvw.ne hvw
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe,
        Finset.mem_sdiff, Finset.mem_biUnion]
      exact Or.inr ⟨v, hvS, (mem_outsideNeighborFinset G).2 ⟨hvw, hwC'⟩⟩
    · left
      simp [hvC, hvS]
  · by_cases hwS : w ∈ S
    · left
      have hvC' : v ∉ C := by
        intro hvC
        exact hI hvC hwC hvw.ne hvw
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe,
        Finset.mem_sdiff, Finset.mem_biUnion]
      exact Or.inr ⟨w, hwS,
        (mem_outsideNeighborFinset G).2 ⟨hvw.symm, hvC'⟩⟩
    · right
      simp [hwC, hwS]

/-- The Hall inequality for an independent minimum-cardinality vertex cover.

The minimum hypothesis is deliberately stated as a comparison with every
finite cover, so callers do not need to unfold the extended-natural-valued
`SimpleGraph.vertexCoverNum`. -/
theorem minimum_vertexCover_hall_outside
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Finset V}
    (hI : G.IsIndepSet (C : Set V))
    (hC : G.IsVertexCover (C : Set V))
    (hmin : ∀ D : Finset V, G.IsVertexCover (D : Set V) → C.card ≤ D.card)
    {S : Finset V} (hSC : S ⊆ C) :
    S.card ≤ (S.biUnion (outsideNeighborFinset G C)).card := by
  let N := S.biUnion (outsideNeighborFinset G C)
  let D := (C \ S) ∪ N
  have hD : G.IsVertexCover (D : Set V) := by
    simpa [D, N] using vertexCover_replace_by_outsideNeighbors G hI hC
  have hcard := hmin D hD
  have hNC : Disjoint N C := by
    rw [Finset.disjoint_left]
    intro v hvN hvC
    simp only [N, Finset.mem_biUnion] at hvN
    obtain ⟨w, hwS, hvout⟩ := hvN
    exact ((mem_outsideNeighborFinset G).1 hvout).2 hvC
  have hdisj : Disjoint (C \ S) N := by
    rw [Finset.disjoint_left]
    intro v hvCS hvN
    exact (Finset.disjoint_left.mp hNC) hvN (Finset.mem_sdiff.mp hvCS).1
  rw [show D = (C \ S) ∪ N by rfl, Finset.card_union_of_disjoint hdisj,
    Finset.card_sdiff_of_subset hSC] at hcard
  change S.card ≤ N.card
  have hSCcard : S.card ≤ C.card := Finset.card_le_card hSC
  omega

/-- Hall's theorem turns the preceding cardinal inequalities into distinct
outside representatives, one adjacent to each vertex of the cover. -/
theorem exists_injective_outsideNeighbor_of_minimum_vertexCover
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Finset V}
    (hI : G.IsIndepSet (C : Set V))
    (hC : G.IsVertexCover (C : Set V))
    (hmin : ∀ D : Finset V, G.IsVertexCover (D : Set V) → C.card ≤ D.card) :
    ∃ f : C → V, Injective f ∧
      ∀ x : C, G.Adj x (f x) ∧ f x ∉ C := by
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun x : C ↦ outsideNeighborFinset G C x)).mp (by
        intro T
        have hT : T.image Subtype.val ⊆ C := by
          intro v hv
          obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
          exact x.property
        have hHall := minimum_vertexCover_hall_outside G hI hC hmin hT
        have hbiUnion :
            (T.image Subtype.val).biUnion (outsideNeighborFinset G C) =
              T.biUnion (fun x : C ↦ outsideNeighborFinset G C x) := by
          ext v
          simp only [Finset.mem_biUnion, Finset.mem_image]
          constructor
          · rintro ⟨w, ⟨x, hxT, rfl⟩, hv⟩
            exact ⟨x, hxT, hv⟩
          · rintro ⟨x, hxT, hv⟩
            exact ⟨x, ⟨x, hxT, rfl⟩, hv⟩
        rw [Finset.card_image_of_injective _ Subtype.val_injective,
          hbiUnion] at hHall
        exact hHall)
  refine ⟨f, hf, ?_⟩
  intro x
  exact (mem_outsideNeighborFinset G).1 (hmem x)

/-- A minimum independent vertex cover is saturated by a matching.  This is
the graph-theoretic packaging of `minimum_vertexCover_hall_outside`. -/
theorem exists_isMatching_saturating_minimum_vertexCover
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Finset V}
    (hI : G.IsIndepSet (C : Set V))
    (hC : G.IsVertexCover (C : Set V))
    (hmin : ∀ D : Finset V, G.IsVertexCover (D : Set V) → C.card ≤ D.card) :
    ∃ M : G.Subgraph, (C : Set V) ⊆ M.verts ∧ M.IsMatching := by
  apply G.exists_isMatching_of_forall_ncard_le
    (isBipartiteWith_of_isIndepSet_isVertexCover G hI hC)
  intro s hsC
  let S := s.toFinset
  let N := S.biUnion (outsideNeighborFinset G C)
  have hSC : S ⊆ C := by
    intro x hxS
    exact hsC (by simpa [S] using hxS)
  have hHall : S.card ≤ N.card := by
    simpa [N] using minimum_vertexCover_hall_outside G hI hC hmin hSC
  have hNsub : (N : Set V) ⊆ ⋃ x ∈ s, G.neighborSet x := by
    intro y hyN
    simp only [N, S, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
      Set.mem_toFinset] at hyN ⊢
    obtain ⟨x, hxs, hyout⟩ := hyN
    exact ⟨x, hxs, (mem_outsideNeighborFinset G).1 hyout |>.1⟩
  calc
    s.ncard = S.card := by simp [S, Set.ncard_eq_toFinset_card']
    _ ≤ N.card := hHall
    _ = (N : Set V).ncard := by simp
    _ ≤ (⋃ x ∈ s, G.neighborSet x).ncard := Set.ncard_le_ncard hNsub

section MaximalMatching

variable {G : SimpleGraph V} {M : G.Subgraph}

omit [Fintype V] [DecidableEq V] in
/-- The endpoints of a maximal matching form a vertex cover.  Maximality is
with respect to inclusion among matching subgraphs. -/
theorem Subgraph.IsMatching.isVertexCover_verts_of_maximal
    (hM : M.IsMatching)
    (hmax : Maximal (fun N : G.Subgraph ↦ N.IsMatching) M) :
    G.IsVertexCover M.verts := by
  intro v w hvw
  by_contra h
  push Not at h
  let E : G.Subgraph := G.subgraphOfAdj hvw
  have hdisj : Disjoint M.support E.support := by
    change Disjoint M.support (G.subgraphOfAdj hvw).support
    rw [SimpleGraph.support_subgraphOfAdj, Set.disjoint_left]
    intro x hxM hxE
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxE
    rcases hxE with rfl | rfl
    · exact h.1 (M.support_subset_verts hxM)
    · exact h.2 (M.support_subset_verts hxM)
  have hME : (M ⊔ E).IsMatching :=
    hM.sup (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj hvw) hdisj
  have hle : M ≤ M ⊔ E := le_sup_left
  have hEM : M ⊔ E ≤ M := hmax.2 hME hle
  have hE : E ≤ M := le_sup_right.trans hEM
  have : M.Adj v w := hE.right (SimpleGraph.subgraphOfAdj_adj_self hvw)
  exact h.1 (M.edge_vert this)

omit [DecidableEq V] in
/-- Every finite graph has a matching whose endpoints form a vertex cover. -/
theorem exists_isMatching_isVertexCover_verts (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ G.IsVertexCover M.verts := by
  classical
  have hbot : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    simp at hv
  obtain ⟨M, -, hmax⟩ :=
    @Finite.exists_le_maximal G.Subgraph _ _ (fun N ↦ N.IsMatching) ⊥ hbot
  exact ⟨M, hmax.1,
    Subgraph.IsMatching.isVertexCover_verts_of_maximal hmax.1 hmax⟩

end MaximalMatching

end Erdos622
