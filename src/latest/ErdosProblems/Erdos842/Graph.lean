/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Erdős Problem 842: the exact graph model

This file records the graph-theoretic model used in the formalization of Erdős Problem 842.
The graph is the exact union of a spanning cycle and a factor of `n` vertex-disjoint triangles.
The disjointness condition says that the cycle edges really are the newly added edges.

The hard part of the problem is to color the canonical graph.  The results here isolate that
statement from all changes of vertex coordinates and provide the final coloring and chromatic-number
transport.
-/

open SimpleGraph

namespace Erdos842

/-- The spanning cycle obtained by transporting the standard cycle on `Fin (3 * n)` along a
chosen ordering of the vertices. -/
def cyclePart {V : Type*} (n : ℕ) (cycleOrder : Fin (3 * n) ≃ V) : SimpleGraph V :=
  (cycleGraph (3 * n)).map cycleOrder.toEmbedding

/-- The factor of `n` vertex-disjoint triangles whose triangle coordinate is the first component
of `triangleCoord`.  It is the complement of the complete `n`-partite graph with parts of size
three, transported to `V`. -/
def triangleFactor {V : Type*} (n : ℕ) (triangleCoord : V ≃ Fin n × Fin 3) :
    SimpleGraph V :=
  ((completeEquipartiteGraph n 3)ᶜ).comap triangleCoord

@[simp]
lemma cyclePart_adj {V : Type*} (n : ℕ) (cycleOrder : Fin (3 * n) ≃ V)
    (u v : Fin (3 * n)) :
    (cyclePart n cycleOrder).Adj (cycleOrder u) (cycleOrder v) ↔
      (cycleGraph (3 * n)).Adj u v := by
  simpa only [cyclePart, Equiv.toEmbedding_apply] using
    (SimpleGraph.map_adj_apply
      (G := cycleGraph (3 * n)) (f := cycleOrder.toEmbedding) (a := u) (b := v))

@[simp]
lemma triangleFactor_adj {V : Type*} (n : ℕ) (triangleCoord : V ≃ Fin n × Fin 3)
    (u v : V) :
    (triangleFactor n triangleCoord).Adj u v ↔
      u ≠ v ∧ (triangleCoord u).1 = (triangleCoord v).1 := by
  simp [triangleFactor, triangleCoord.injective.eq_iff]

/-- The canonical representative in cycle coordinates.  Its triangle factor can be arbitrary:
`triangleCoord` records which triples of cycle positions form the original triangles. -/
def canonicalGraph (n : ℕ) (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    SimpleGraph (Fin (3 * n)) :=
  cycleGraph (3 * n) ⊔ triangleFactor n triangleCoord

/-- `G` is exactly a graph obtained from `n` vertex-disjoint triangles by adding every edge of a
Hamiltonian cycle.  The two displayed parts are edge-disjoint, expressing that every cycle edge
is a new edge, and the equality rules out any additional edges. -/
def IsCyclePlusTriangles {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (cycleOrder : Fin (3 * n) ≃ V) (triangleCoord : V ≃ Fin n × Fin 3),
    Disjoint (cyclePart n cycleOrder) (triangleFactor n triangleCoord) ∧
      G = cyclePart n cycleOrder ⊔ triangleFactor n triangleCoord

lemma map_sup_equiv {V W : Type*} (e : V ≃ W) (G H : SimpleGraph V) :
    (G ⊔ H).map e.toEmbedding = G.map e.toEmbedding ⊔ H.map e.toEmbedding := by
  ext u v
  simp only [SimpleGraph.map_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨a, b, hab | hab, rfl, rfl⟩
    · exact Or.inl ⟨a, b, hab, rfl, rfl⟩
    · exact Or.inr ⟨a, b, hab, rfl, rfl⟩
  · rintro (⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩)
    · exact ⟨a, b, Or.inl hab, rfl, rfl⟩
    · exact ⟨a, b, Or.inr hab, rfl, rfl⟩

lemma disjoint_map_equiv_iff {V W : Type*} (e : V ≃ W) (G H : SimpleGraph V) :
    Disjoint (G.map e.toEmbedding) (H.map e.toEmbedding) ↔ Disjoint G H := by
  rw [disjoint_iff_inf_le, disjoint_iff_inf_le]
  constructor
  · intro h u v huv
    exact h ⟨SimpleGraph.map_adj_apply.mpr huv.1, SimpleGraph.map_adj_apply.mpr huv.2⟩
  · intro h u v huv
    obtain ⟨a, b, hab, ha, hb⟩ :=
      (SimpleGraph.map_adj e.toEmbedding G u v).mp huv.1
    subst u
    subst v
    exact h ⟨hab, SimpleGraph.map_adj_apply.mp huv.2⟩

lemma triangleFactor_map {V : Type*} (n : ℕ) (cycleOrder : Fin (3 * n) ≃ V)
    (triangleCoord : V ≃ Fin n × Fin 3) :
    (triangleFactor n (cycleOrder.trans triangleCoord)).map cycleOrder.toEmbedding =
      triangleFactor n triangleCoord := by
  ext u v
  simp only [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    simpa using hab
  · intro huv
    exact ⟨cycleOrder.symm u, cycleOrder.symm v, by simpa using huv, by simp, by simp⟩

/-- Transporting the canonical graph along its cycle ordering gives exactly the displayed union
on the original vertex type. -/
lemma canonicalGraph_map {V : Type*} (n : ℕ) (cycleOrder : Fin (3 * n) ≃ V)
    (triangleCoord : V ≃ Fin n × Fin 3) :
    (canonicalGraph n (cycleOrder.trans triangleCoord)).map cycleOrder.toEmbedding =
      cyclePart n cycleOrder ⊔ triangleFactor n triangleCoord := by
  rw [canonicalGraph, map_sup_equiv, triangleFactor_map]
  rfl

/-- Every graph satisfying the exact public model is a transported canonical graph. -/
lemma IsCyclePlusTriangles.exists_eq_map_canonical {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (hG : IsCyclePlusTriangles G n) :
    ∃ (cycleOrder : Fin (3 * n) ≃ V) (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3),
      G = (canonicalGraph n triangleCoord).map cycleOrder.toEmbedding := by
  obtain ⟨cycleOrder, triangleCoord, -, hG⟩ := hG
  refine ⟨cycleOrder, cycleOrder.trans triangleCoord, ?_⟩
  rw [canonicalGraph_map]
  exact hG

/-- The canonical graph associated with a graph satisfying the public model has an edge-disjoint
cycle and triangle factor. -/
lemma IsCyclePlusTriangles.exists_disjoint_canonical {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (hG : IsCyclePlusTriangles G n) :
    ∃ (cycleOrder : Fin (3 * n) ≃ V) (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3),
      Disjoint (cycleGraph (3 * n)) (triangleFactor n triangleCoord) ∧
        G = (canonicalGraph n triangleCoord).map cycleOrder.toEmbedding := by
  obtain ⟨cycleOrder, triangleCoord, hdisj, hG⟩ := hG
  refine ⟨cycleOrder, cycleOrder.trans triangleCoord, ?_, ?_⟩
  · rw [← triangleFactor_map n cycleOrder triangleCoord] at hdisj
    exact (disjoint_map_equiv_iff cycleOrder (cycleGraph (3 * n))
      (triangleFactor n (cycleOrder.trans triangleCoord))).mp hdisj
  · rw [canonicalGraph_map]
    exact hG

/-- Exact canonical characterization of the public graph model.  In particular, the canonical
reduction neither loses the condition that the cycle edges are new nor introduces extra edges. -/
lemma isCyclePlusTriangles_iff_exists_map_canonical
    {V : Type*} {G : SimpleGraph V} {n : ℕ} :
    IsCyclePlusTriangles G n ↔
      ∃ (cycleOrder : Fin (3 * n) ≃ V)
          (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3),
        Disjoint (cycleGraph (3 * n)) (triangleFactor n triangleCoord) ∧
          G = (canonicalGraph n triangleCoord).map cycleOrder.toEmbedding := by
  constructor
  · exact IsCyclePlusTriangles.exists_disjoint_canonical
  · rintro ⟨cycleOrder, triangleCoord, hdisj, hG⟩
    let transportedCoord : V ≃ Fin n × Fin 3 := cycleOrder.symm.trans triangleCoord
    have hcoord : cycleOrder.trans transportedCoord = triangleCoord := by
      apply Equiv.ext
      intro u
      simp [transportedCoord]
    refine ⟨cycleOrder, transportedCoord, ?_, ?_⟩
    · rw [← triangleFactor_map n cycleOrder transportedCoord, hcoord]
      exact (disjoint_map_equiv_iff cycleOrder (cycleGraph (3 * n))
        (triangleFactor n triangleCoord)).mpr hdisj
    · calc
        G = (canonicalGraph n triangleCoord).map cycleOrder.toEmbedding := hG
        _ = (canonicalGraph n (cycleOrder.trans transportedCoord)).map
            cycleOrder.toEmbedding := by rw [hcoord]
        _ = cyclePart n cycleOrder ⊔ triangleFactor n transportedCoord :=
          canonicalGraph_map n cycleOrder transportedCoord

/-- Colorability is invariant under transporting a graph along an equivalence of vertex types. -/
lemma colorable_map_equiv_iff {V W : Type*} (e : V ≃ W) (G : SimpleGraph V) (k : ℕ) :
    (G.map e.toEmbedding).Colorable k ↔ G.Colorable k :=
  (SimpleGraph.colorable_congr (SimpleGraph.Iso.map e G)).symm

/-- A coloring theorem for every canonical graph implies the corresponding theorem for every
graph satisfying the exact public model. -/
lemma IsCyclePlusTriangles.colorable_of_canonical {V : Type*} {G : SimpleGraph V} {n k : ℕ}
    (hG : IsCyclePlusTriangles G n)
    (hcanonical : ∀ triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3,
      Disjoint (cycleGraph (3 * n)) (triangleFactor n triangleCoord) →
        (canonicalGraph n triangleCoord).Colorable k) :
    G.Colorable k := by
  obtain ⟨cycleOrder, triangleCoord, hdisj, hG⟩ := hG.exists_disjoint_canonical
  rw [hG, colorable_map_equiv_iff]
  exact hcanonical triangleCoord hdisj

/-- Chromatic-number form of `IsCyclePlusTriangles.colorable_of_canonical`. -/
lemma IsCyclePlusTriangles.chromaticNumber_le_of_canonical
    {V : Type*} {G : SimpleGraph V} {n k : ℕ}
    (hG : IsCyclePlusTriangles G n)
    (hcanonical : ∀ triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3,
      Disjoint (cycleGraph (3 * n)) (triangleFactor n triangleCoord) →
        (canonicalGraph n triangleCoord).Colorable k) :
    G.chromaticNumber ≤ k := by
  exact SimpleGraph.chromaticNumber_le_iff_colorable.mpr
    (hG.colorable_of_canonical hcanonical)

end Erdos842
