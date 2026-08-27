/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyVertexRestriction
import ErdosProblems.Erdos207.RegularizationGraphEncoding

/-! # Exact edge and pair-degree transport to the current vertex universe -/

namespace Erdos207

open Finset

noncomputable section

theorem sym2Map_mem_tripleEdgeFinset_iff
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (e : Sym2 V) (T : TripleOn V) :
    f.sym2Map e ∈ tripleEdgeFinset (mapTriple f T) ↔ e ∈ tripleEdgeFinset T := by
  refine Sym2.inductionOn e (fun x y ↦ ?_)
  change s(f x, f y) ∈ tripleEdgeFinset (mapTriple f T) ↔ s(x, y) ∈ tripleEdgeFinset T
  simp only [mk_mem_tripleEdgeFinset_iff, mem_mapTriple_apply_iff, f.injective.ne_iff]

theorem graphEdges_induce_map
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (D : Finset V)
    (hG : GraphSupportedOn G (D : Set V)) :
    (graphEdges (G.induce (D : Set V))).map
      (Function.Embedding.subtype (fun v ↦ v ∈ D)).sym2Map = graphEdges G := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := mem_map.mp he
    revert hf
    refine Sym2.inductionOn f (fun x y hf ↦ ?_)
    change s(x.val, y.val) ∈ graphEdges G
    have hadj : (G.induce (D : Set V)).Adj x y := mem_graphEdges_iff.mp hf
    exact mem_graphEdges_iff.mpr hadj
  · intro he
    revert he
    refine Sym2.inductionOn e (fun x y he ↦ ?_)
    have hxy : G.Adj x y := mem_graphEdges_iff.mp he
    have hx := (hG hxy).1
    have hy := (hG hxy).2
    exact mem_map.mpr ⟨s(⟨x, hx⟩, ⟨y, hy⟩), mem_graphEdges_iff.mpr hxy, rfl⟩

theorem card_graphEdges_induce
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (D : Finset V)
    (hG : GraphSupportedOn G (D : Set V)) :
    (graphEdges (G.induce (D : Set V))).card = (graphEdges G).card := by
  rw [← graphEdges_induce_map G D hG, card_map]

theorem mapped_triangle_edge_count
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (A : TripleSystemOn V) (e : Sym2 V) :
    ((mapTripleSystem f A).filter (fun T ↦ f.sym2Map e ∈ tripleEdgeFinset T)).card =
      (A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card := by
  have hset : (mapTripleSystem f A).filter (fun T ↦ f.sym2Map e ∈ tripleEdgeFinset T) =
      mapTripleSystem f (A.filter (fun T ↦ e ∈ tripleEdgeFinset T)) := by
    ext T
    simp only [mem_filter, mapTripleSystem, mem_map]
    constructor
    · rintro ⟨⟨S, hS, rfl⟩, he⟩
      exact ⟨S, ⟨hS, (sym2Map_mem_tripleEdgeFinset_iff f e S).mp he⟩, rfl⟩
    · rintro ⟨S, ⟨hS, he⟩, rfl⟩
      exact ⟨⟨S, hS, rfl⟩, (sym2Map_mem_tripleEdgeFinset_iff f e S).mpr he⟩
  rw [hset, card_mapTripleSystem]

theorem restricted_triangle_edge_count
    {V : Type*} [Fintype V] [DecidableEq V] (D : Finset V) (A : TripleSystemOn V)
    (hA : ∀ T ∈ A, T.1 ⊆ D) (e : Sym2 D) :
    ((restrictTripleSystemTo D A).filter (fun T ↦ e ∈ tripleEdgeFinset T)).card =
      (A.filter (fun T ↦ (Function.Embedding.subtype (fun v ↦ v ∈ D)).sym2Map e ∈
        tripleEdgeFinset T)).card := by
  rw [← mapped_triangle_edge_count (Function.Embedding.subtype (fun v ↦ v ∈ D)),
    map_restrictTripleSystemTo D A hA]

theorem restricted_triangle_edges_induce
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (D : Finset V)
    (A : TripleSystemOn V) (htri : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) :
    ∀ T ∈ restrictTripleSystemTo D A, tripleEdgeFinset T ⊆ graphEdges (G.induce (D : Set V)) := by
  intro T hT e he
  have hambient := htri (mapTriple (Function.Embedding.subtype (fun v ↦ v ∈ D)) T)
    ((mem_restrictTripleSystemTo D A T).mp hT)
    ((sym2Map_mem_tripleEdgeFinset_iff (Function.Embedding.subtype (fun v ↦ v ∈ D)) e T).mpr he)
  revert hambient
  refine Sym2.inductionOn e (fun x y hxy ↦ ?_)
  have hadj : G.Adj x.val y.val := mem_graphEdges_iff.mp hxy
  exact mem_graphEdges_iff.mpr hadj

theorem restricted_triangle_pair_regularity
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (D : Finset V)
    (A : TripleSystemOn V) (target theta : ℝ)
    (hA : ∀ T ∈ A, T.1 ⊆ D)
    (hreg : ∀ e ∈ graphEdges G,
      |((A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) - target| ≤ theta * target) :
    ∀ e ∈ graphEdges (G.induce (D : Set V)),
      |(((restrictTripleSystemTo D A).filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) - target| ≤
        theta * target := by
  intro e he
  have hcount := restricted_triangle_edge_count D A hA e
  have hcountR : (((restrictTripleSystemTo D A).filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) =
      ((A.filter (fun T ↦ (Function.Embedding.subtype (fun v ↦ v ∈ D)).sym2Map e ∈
        tripleEdgeFinset T)).card : ℝ) := by exact_mod_cast hcount
  calc
    _ = |((A.filter (fun T ↦ (Function.Embedding.subtype (fun v ↦ v ∈ D)).sym2Map e ∈
        tripleEdgeFinset T)).card : ℝ) - target| := by congr 2
    _ ≤ theta * target := ?_
  apply hreg
  revert he
  refine Sym2.inductionOn e (fun x y hxy ↦ ?_)
  have hadj : (G.induce (D : Set V)).Adj x y := mem_graphEdges_iff.mp hxy
  exact mem_graphEdges_iff.mpr hadj

end

end Erdos207
