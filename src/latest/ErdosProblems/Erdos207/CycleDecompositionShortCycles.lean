/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ShortCycleGrouping
import Mathlib.Data.Fintype.Lattice

/-!
# The short-cycle family of a cycle decomposition

This file turns the recursive path-cover expansion into one finite indexed
family of triangles, four-cycles, and five-cycles.  The heterogeneous walks
stored by a `CycleDecomposition` are first packaged into uniform records.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Different universal path-cover slots are edge-disjoint. -/
lemma pathCoverSlotGraph_disjoint
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    {i j : Fin k} (hij : i ≠ j) :
    Disjoint (pathCoverSlotGraph (V := V) i)
      (pathCoverSlotGraph (V := V) j) := by
  rw [SimpleGraph.disjoint_left]
  intro u v huv huv'
  simp only [pathCoverSlotGraph, SimpleGraph.iSup_adj,
    pathCoverPathAtEdge, pathCoverTwoEdgePath_adj_iff] at huv huv'
  obtain ⟨e, he⟩ := huv
  obtain ⟨f, hf⟩ := huv'
  rcases he with he | he | he | he <;>
    rcases hf with hf | hf | hf | hf <;>
    rcases he with ⟨he₁, he₂⟩ <;>
    rcases hf with ⟨hf₁, hf₂⟩ <;>
    simp_all [pathCoverMiddleBetween]

/-- Root-root edges are disjoint from every path-cover slot. -/
lemma rootMap_disjoint_pathCoverSlotGraph
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (i : Fin k) :
    Disjoint (G.map (pathCoverRootEmbedding (X := V) (k := k)))
      (pathCoverSlotGraph (V := V) i) := by
  rw [SimpleGraph.disjoint_left]
  intro u v huv huv'
  rw [SimpleGraph.map_adj] at huv
  obtain ⟨a, b, hab, rfl, rfl⟩ := huv
  simp only [pathCoverSlotGraph, SimpleGraph.iSup_adj,
    pathCoverPathAtEdge, pathCoverTwoEdgePath_adj_iff] at huv'
  obtain ⟨e, he⟩ := huv'
  rcases he with he | he | he | he <;>
    rcases he with ⟨he₁, he₂⟩ <;>
    simp_all [pathCoverMiddleBetween, pathCoverRootEmbedding]

/-- A simple closed walk together with its ambient graph, packaged so cycles
from different stages of a recursive decomposition have one common type. -/
structure CycleRecord (V : Type*) where
  ambient : SimpleGraph V
  vertex : V
  walk : ambient.Walk vertex vertex
  isCycle : walk.IsCycle

namespace CycleDecomposition

/-- Cycle number `c` in the tail-first ordering used by the path-slot
allocation.  The current cycle of a `step` is the last index. -/
def cycleRecordAt
    {V : Type*} {G : SimpleGraph V} (D : CycleDecomposition G) :
    Fin D.cycleCount → CycleRecord V :=
  match D with
  | .empty => Fin.elim0
  | @step _ G v p hp tail =>
      Fin.lastCases ⟨G, v, p, hp⟩ (cycleRecordAt tail)

@[simp]
lemma cycleRecordAt_step_last
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle)
    (tail : CycleDecomposition (G \ p.toSubgraph.spanningCoe)) :
    (CycleDecomposition.step p hp tail).cycleRecordAt
        (Fin.last tail.cycleCount) = ⟨G, v, p, hp⟩ := by
  simp [cycleRecordAt]

@[simp]
lemma cycleRecordAt_step_castSucc
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle)
    (tail : CycleDecomposition (G \ p.toSubgraph.spanningCoe))
    (c : Fin tail.cycleCount) :
    (CycleDecomposition.step p hp tail).cycleRecordAt c.castSucc =
      tail.cycleRecordAt c := by
  simp [cycleRecordAt]

/-- The exact old root graph carried by one indexed cycle. -/
def cycleRootGraphAt
    {V : Type*} {G : SimpleGraph V} (D : CycleDecomposition G)
    (c : Fin D.cycleCount) : SimpleGraph V :=
  let R := D.cycleRecordAt c
  R.walk.toSubgraph.spanningCoe

@[simp]
lemma cycleRootGraphAt_step_last
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle)
    (tail : CycleDecomposition (G \ p.toSubgraph.spanningCoe)) :
    (CycleDecomposition.step p hp tail).cycleRootGraphAt
        (Fin.last tail.cycleCount) = p.toSubgraph.spanningCoe := by
  unfold cycleRootGraphAt
  rw [cycleRecordAt_step_last]

@[simp]
lemma cycleRootGraphAt_step_castSucc
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle)
    (tail : CycleDecomposition (G \ p.toSubgraph.spanningCoe))
    (c : Fin tail.cycleCount) :
    (CycleDecomposition.step p hp tail).cycleRootGraphAt c.castSucc =
      tail.cycleRootGraphAt c := by
  unfold cycleRootGraphAt
  rw [cycleRecordAt_step_castSucc]

/-- Every cycle root stored in a decomposition is a subgraph of the graph
being decomposed. -/
lemma cycleRootGraphAt_le
    {V : Type*} {G : SimpleGraph V} (D : CycleDecomposition G)
    (c : Fin D.cycleCount) : D.cycleRootGraphAt c ≤ G := by
  induction D with
  | empty => exact Fin.elim0 c
  | @step G v p hp tail ih =>
      cases c using Fin.lastCases with
      | last =>
          simpa using walkSpanningCoe_le p
      | cast c =>
          have htail : tail.cycleRootGraphAt c ≤
              G \ p.toSubgraph.spanningCoe := ih c
          simpa using htail.trans sdiff_le

/-- Distinct recursive cycle roots are edge-disjoint. -/
lemma cycleRootGraphAt_pairwiseDisjoint
    {V : Type*} {G : SimpleGraph V} (D : CycleDecomposition G)
    {c d : Fin D.cycleCount} (hcd : c ≠ d) :
    Disjoint (D.cycleRootGraphAt c) (D.cycleRootGraphAt d) := by
  induction D with
  | empty => exact Fin.elim0 c
  | @step G v p hp tail ih =>
      cases c using Fin.lastCases with
      | last =>
          cases d using Fin.lastCases with
          | last => exact (hcd rfl).elim
          | cast d =>
              simp only [cycleRootGraphAt_step_last,
                cycleRootGraphAt_step_castSucc]
              exact disjoint_sdiff_self_right.mono_right
                (tail.cycleRootGraphAt_le d)
      | cast c =>
          cases d using Fin.lastCases with
          | last =>
              simp only [cycleRootGraphAt_step_last,
                cycleRootGraphAt_step_castSucc]
              exact disjoint_sdiff_self_left.mono_left
                (tail.cycleRootGraphAt_le c)
          | cast d =>
              simp only [cycleRootGraphAt_step_castSucc]
              apply ih
              intro h
              exact hcd (Fin.castSucc_inj.mpr h)

/-- The complete augmented graph attached to indexed cycle `c`. -/
def indexedCycleAugmentedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) (c : Fin D.cycleCount) :
    SimpleGraph (PathCoverVertex V (6 * m ^ 2)) :=
  let R := D.cycleRecordAt c
  cycleAugmentedPieceGraph m c.1 (lt_trans c.2 hD)
    R.walk R.isCycle

lemma indexedCycleAugmentedGraph_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) (c : Fin D.cycleCount) :
    D.indexedCycleAugmentedGraph m hD c =
      (D.cycleRootGraphAt c).map
          (pathCoverRootEmbedding (X := V) (k := 6 * m ^ 2)) ⊔
        (pathCoverSlotGraph
            (firstCyclePathSlot m c.1 (lt_trans c.2 hD)) ⊔
          pathCoverSlotGraph
            (secondCyclePathSlot m c.1 (lt_trans c.2 hD))) := by
  unfold indexedCycleAugmentedGraph cycleRootGraphAt
  rw [cycleAugmentedPieceGraph_eq,
    map_walkCyclePathRootEmbedding_eq]

lemma indexedCycleAugmentedGraph_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    {c d : Fin D.cycleCount} (hcd : c ≠ d) :
    Disjoint (D.indexedCycleAugmentedGraph m hD c)
      (D.indexedCycleAugmentedGraph m hD d) := by
  rw [indexedCycleAugmentedGraph_eq, indexedCycleAugmentedGraph_eq,
    disjoint_sup_left, disjoint_sup_right,
    disjoint_sup_right, disjoint_sup_left]
  let c' : Fin (m ^ 2) := ⟨c.1, lt_trans c.2 hD⟩
  let d' : Fin (m ^ 2) := ⟨d.1, lt_trans d.2 hD⟩
  have hcd' : c' ≠ d' := by
    intro h
    have hv : c.1 = d.1 := by
      simpa [c', d'] using congrArg Fin.val h
    exact hcd (Fin.ext hv)
  have hslots := cyclePathSlots_ne m hcd'
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact SimpleGraph.disjoint_map_embedding _
      (D.cycleRootGraphAt_pairwiseDisjoint hcd)
  · exact rootMap_disjoint_pathCoverSlotGraph _ _
  · exact rootMap_disjoint_pathCoverSlotGraph _ _
  · rw [disjoint_sup_right, disjoint_sup_right]
    exact ⟨(rootMap_disjoint_pathCoverSlotGraph _ _).symm,
      pathCoverSlotGraph_disjoint hslots.1,
      pathCoverSlotGraph_disjoint hslots.2.1⟩
  · rw [disjoint_sup_right, disjoint_sup_right]
    exact ⟨(rootMap_disjoint_pathCoverSlotGraph _ _).symm,
      pathCoverSlotGraph_disjoint hslots.2.2.1,
      pathCoverSlotGraph_disjoint hslots.2.2.2⟩

abbrev DecompositionTriangleIndex
    {V : Type*} {G : SimpleGraph V} (D : CycleDecomposition G) :=
  Σ _c : Fin D.cycleCount, Bool

abbrev DecompositionFiveCycleIndex
    {V : Type*} {G : SimpleGraph V} (D : CycleDecomposition G) :=
  Σ c : Fin D.cycleCount,
    Fin ((D.cycleRecordAt c).walk.length - 2)

abbrev DecompositionResidualFourIndex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : CycleDecomposition G) :=
  Σ c : Fin D.cycleCount,
    CycleResidualEdge (D.cycleRecordAt c).walk
      (D.cycleRecordAt c).isCycle

abbrev DecompositionUnusedFourIndex
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G) :=
  (SimpleGraph.completeGraph V).edgeSet ×
    Fin (unusedPathPairCount m D.cycleCount)

abbrev DecompositionFourCycleIndex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G) :=
  DecompositionResidualFourIndex D ⊕
    DecompositionUnusedFourIndex m D

def decompositionTriangleEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) (x : DecompositionTriangleIndex D) :
    Fin 3 ↪ PathCoverVertex V (6 * m ^ 2) :=
  let R := D.cycleRecordAt x.1
  if x.2 then
    firstCycleEndpointTriangle m x.1.1 (lt_trans x.1.2 hD)
      R.walk R.isCycle
  else
    lastCycleEndpointTriangle m x.1.1 (lt_trans x.1.2 hD)
      R.walk R.isCycle

def decompositionFiveCycleEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) (x : DecompositionFiveCycleIndex D) :
    Fin 5 ↪ PathCoverVertex V (6 * m ^ 2) :=
  let R := D.cycleRecordAt x.1
  cycleChainC5 m x.1.1 (lt_trans x.1.2 hD)
    R.walk R.isCycle x.2

def decompositionFourCycleEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    (x : DecompositionFourCycleIndex m D) :
    Fin 4 ↪ PathCoverVertex V (6 * m ^ 2) :=
  match x with
  | .inl x =>
      let R := D.cycleRecordAt x.1
      cycleResidualC4 m x.1.1 (lt_trans x.1.2 hD)
        R.walk R.isCycle x.2
  | .inr x =>
      unusedPathC4 m D.cycleCount hD.le x.1 x.2

/-- The concrete short-cycle family produced by all augmented cycles and all
unused path pairs. -/
def shortCycleFamily
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) :
    ShortCycleFamily (PathCoverVertex V (6 * m ^ 2))
      (DecompositionTriangleIndex D)
      (DecompositionFourCycleIndex m D)
      (DecompositionFiveCycleIndex D) where
  triangle := decompositionTriangleEmbedding m D hD
  fourCycle := decompositionFourCycleEmbedding m D hD
  fiveCycle := decompositionFiveCycleEmbedding m D hD

noncomputable instance instDecidableEqDecompositionShortCycleIndex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G) :
    DecidableEq
      (ShortCycleIndex (DecompositionTriangleIndex D)
        (DecompositionFourCycleIndex m D)
        (DecompositionFiveCycleIndex D)) :=
  Classical.decEq _

lemma decompositionTriangle_le_indexedCycleAugmentedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) (x : DecompositionTriangleIndex D) :
    (SimpleGraph.cycleGraph 3).map
        (decompositionTriangleEmbedding m D hD x) ≤
      D.indexedCycleAugmentedGraph m hD x.1 := by
  rcases x with ⟨c, b⟩
  cases b <;> simp only [decompositionTriangleEmbedding, ↓reduceIte]
  · unfold indexedCycleAugmentedGraph cycleAugmentedPieceGraph
    exact le_sup_of_le_left (le_sup_of_le_right le_sup_left)
  · unfold indexedCycleAugmentedGraph cycleAugmentedPieceGraph
    exact le_sup_of_le_left le_sup_left

lemma decompositionFiveCycle_le_indexedCycleAugmentedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) (x : DecompositionFiveCycleIndex D) :
    (SimpleGraph.cycleGraph 5).map
        (decompositionFiveCycleEmbedding m D hD x) ≤
      D.indexedCycleAugmentedGraph m hD x.1 := by
  rcases x with ⟨c, i⟩
  let R := D.cycleRecordAt c
  change (SimpleGraph.cycleGraph 5).map
      (cycleChainC5 m c.1 (lt_trans c.2 hD) R.walk R.isCycle i) ≤
    cycleAugmentedPieceGraph m c.1 (lt_trans c.2 hD)
      R.walk R.isCycle
  unfold cycleAugmentedPieceGraph cycleShortPieceGraph
  have hi :
      (SimpleGraph.cycleGraph 5).map
          (cycleChainC5 m c.1 (lt_trans c.2 hD) R.walk R.isCycle i) ≤
        ⨆ j : Fin (R.walk.length - 2),
          (SimpleGraph.cycleGraph 5).map
            (cycleChainC5 m c.1 (lt_trans c.2 hD)
              R.walk R.isCycle j) :=
    le_iSup (fun j : Fin (R.walk.length - 2) =>
      (SimpleGraph.cycleGraph 5).map
        (cycleChainC5 m c.1 (lt_trans c.2 hD)
          R.walk R.isCycle j)) i
  exact le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_right hi))

lemma decompositionResidualFour_le_indexedCycleAugmentedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    (x : DecompositionResidualFourIndex D) :
    (SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inl x)) ≤
      D.indexedCycleAugmentedGraph m hD x.1 := by
  rcases x with ⟨c, e⟩
  let R := D.cycleRecordAt c
  change (SimpleGraph.cycleGraph 4).map
      (cycleResidualC4 m c.1 (lt_trans c.2 hD) R.walk R.isCycle e) ≤
    cycleAugmentedPieceGraph m c.1 (lt_trans c.2 hD)
      R.walk R.isCycle
  unfold cycleAugmentedPieceGraph cycleResidualGraph
  have he :
      (SimpleGraph.cycleGraph 4).map
          (cycleResidualC4 m c.1 (lt_trans c.2 hD)
            R.walk R.isCycle e) ≤
        ⨆ f : CycleResidualEdge R.walk R.isCycle,
          (SimpleGraph.cycleGraph 4).map
            (cycleResidualC4 m c.1 (lt_trans c.2 hD)
              R.walk R.isCycle f) :=
    le_iSup (fun f : CycleResidualEdge R.walk R.isCycle =>
      (SimpleGraph.cycleGraph 4).map
        (cycleResidualC4 m c.1 (lt_trans c.2 hD)
          R.walk R.isCycle f)) e
  exact le_sup_of_le_right he

lemma decompositionUnusedFour_le_unusedPathGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    (x : DecompositionUnusedFourIndex m D) :
    (SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inr x)) ≤
      unusedPathGraph (V := V) m D.cycleCount hD.le := by
  rcases x with ⟨e, t⟩
  change (SimpleGraph.cycleGraph 4).map
      (unusedPathC4 m D.cycleCount hD.le e t) ≤
    unusedPathGraph (V := V) m D.cycleCount hD.le
  unfold unusedPathGraph
  have ht :
      (SimpleGraph.cycleGraph 4).map
          (unusedPathC4 m D.cycleCount hD.le e t) ≤
        ⨆ u : Fin (unusedPathPairCount m D.cycleCount),
          (SimpleGraph.cycleGraph 4).map
            (unusedPathC4 m D.cycleCount hD.le e u) :=
    le_iSup (fun u : Fin (unusedPathPairCount m D.cycleCount) =>
      (SimpleGraph.cycleGraph 4).map
        (unusedPathC4 m D.cycleCount hD.le e u)) t
  exact ht.trans (le_iSup (fun f =>
    ⨆ u : Fin (unusedPathPairCount m D.cycleCount),
      (SimpleGraph.cycleGraph 4).map
        (unusedPathC4 m D.cycleCount hD.le f u)) e)

lemma decompositionTriangle_pairwise_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    {x y : DecompositionTriangleIndex D} (hxy : x ≠ y) :
    Disjoint
      ((SimpleGraph.cycleGraph 3).map
        (decompositionTriangleEmbedding m D hD x))
      ((SimpleGraph.cycleGraph 3).map
        (decompositionTriangleEmbedding m D hD y)) := by
  rcases x with ⟨c, b⟩
  rcases y with ⟨d, b'⟩
  by_cases hcd : c = d
  · subst d
    let R := D.cycleRecordAt c
    cases b <;> cases b'
    · exact (hxy rfl).elim
    · simpa [decompositionTriangleEmbedding] using
        (cycleEndpointTriangles_disjoint m c.1 (lt_trans c.2 hD)
          R.walk R.isCycle).symm
    · simpa [decompositionTriangleEmbedding] using
        cycleEndpointTriangles_disjoint m c.1 (lt_trans c.2 hD)
          R.walk R.isCycle
    · exact (hxy rfl).elim
  · exact (D.indexedCycleAugmentedGraph_pairwiseDisjoint m hD hcd).mono
      (decompositionTriangle_le_indexedCycleAugmentedGraph m D hD ⟨c, b⟩)
      (decompositionTriangle_le_indexedCycleAugmentedGraph m D hD ⟨d, b'⟩)

lemma decompositionTriangle_disjoint_fiveCycle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    (x : DecompositionTriangleIndex D)
    (y : DecompositionFiveCycleIndex D) :
    Disjoint
      ((SimpleGraph.cycleGraph 3).map
        (decompositionTriangleEmbedding m D hD x))
      ((SimpleGraph.cycleGraph 5).map
        (decompositionFiveCycleEmbedding m D hD y)) := by
  rcases x with ⟨c, b⟩
  rcases y with ⟨d, i⟩
  by_cases hcd : c = d
  · subst d
    let R := D.cycleRecordAt c
    cases b
    · simpa [decompositionTriangleEmbedding,
          decompositionFiveCycleEmbedding] using
        lastCycleEndpointTriangle_disjoint_cycleChainC5
          m c.1 (lt_trans c.2 hD) R.walk R.isCycle i
    · simpa [decompositionTriangleEmbedding,
          decompositionFiveCycleEmbedding] using
        firstCycleEndpointTriangle_disjoint_cycleChainC5
          m c.1 (lt_trans c.2 hD) R.walk R.isCycle i
  · exact (D.indexedCycleAugmentedGraph_pairwiseDisjoint m hD hcd).mono
      (decompositionTriangle_le_indexedCycleAugmentedGraph m D hD ⟨c, b⟩)
      (decompositionFiveCycle_le_indexedCycleAugmentedGraph m D hD ⟨d, i⟩)

lemma decompositionTriangle_disjoint_residualFour
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    (x : DecompositionTriangleIndex D)
    (y : DecompositionResidualFourIndex D) :
    Disjoint
      ((SimpleGraph.cycleGraph 3).map
        (decompositionTriangleEmbedding m D hD x))
      ((SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inl y))) := by
  rcases x with ⟨c, b⟩
  rcases y with ⟨d, e⟩
  by_cases hcd : c = d
  · subst d
    let R := D.cycleRecordAt c
    cases b
    · simpa [decompositionTriangleEmbedding,
          decompositionFourCycleEmbedding] using
        (cycleResidualC4_disjoint_lastCycleEndpointTriangle
          m c.1 (lt_trans c.2 hD) R.walk R.isCycle e).symm
    · simpa [decompositionTriangleEmbedding,
          decompositionFourCycleEmbedding] using
        (cycleResidualC4_disjoint_firstCycleEndpointTriangle
          m c.1 (lt_trans c.2 hD) R.walk R.isCycle e).symm
  · exact (D.indexedCycleAugmentedGraph_pairwiseDisjoint m hD hcd).mono
      (decompositionTriangle_le_indexedCycleAugmentedGraph m D hD ⟨c, b⟩)
      (decompositionResidualFour_le_indexedCycleAugmentedGraph m D hD ⟨d, e⟩)

lemma decompositionFiveCycle_pairwise_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    {x y : DecompositionFiveCycleIndex D} (hxy : x ≠ y) :
    Disjoint
      ((SimpleGraph.cycleGraph 5).map
        (decompositionFiveCycleEmbedding m D hD x))
      ((SimpleGraph.cycleGraph 5).map
        (decompositionFiveCycleEmbedding m D hD y)) := by
  rcases x with ⟨c, i⟩
  rcases y with ⟨d, j⟩
  by_cases hcd : c = d
  · subst d
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hxy rfl
    let R := D.cycleRecordAt c
    simpa [decompositionFiveCycleEmbedding] using
      cycleChainC5_pairwise_disjoint m c.1 (lt_trans c.2 hD)
        R.walk R.isCycle hij
  · exact (D.indexedCycleAugmentedGraph_pairwiseDisjoint m hD hcd).mono
      (decompositionFiveCycle_le_indexedCycleAugmentedGraph m D hD ⟨c, i⟩)
      (decompositionFiveCycle_le_indexedCycleAugmentedGraph m D hD ⟨d, j⟩)

lemma decompositionFiveCycle_disjoint_residualFour
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    (x : DecompositionFiveCycleIndex D)
    (y : DecompositionResidualFourIndex D) :
    Disjoint
      ((SimpleGraph.cycleGraph 5).map
        (decompositionFiveCycleEmbedding m D hD x))
      ((SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inl y))) := by
  rcases x with ⟨c, i⟩
  rcases y with ⟨d, e⟩
  by_cases hcd : c = d
  · subst d
    let R := D.cycleRecordAt c
    simpa [decompositionFiveCycleEmbedding,
        decompositionFourCycleEmbedding] using
      (cycleResidualC4_disjoint_cycleChainC5
        m c.1 (lt_trans c.2 hD) R.walk R.isCycle e i).symm
  · exact (D.indexedCycleAugmentedGraph_pairwiseDisjoint m hD hcd).mono
      (decompositionFiveCycle_le_indexedCycleAugmentedGraph m D hD ⟨c, i⟩)
      (decompositionResidualFour_le_indexedCycleAugmentedGraph m D hD ⟨d, e⟩)

lemma decompositionResidualFour_pairwise_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    {x y : DecompositionResidualFourIndex D} (hxy : x ≠ y) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inl x)))
      ((SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inl y))) := by
  rcases x with ⟨c, e⟩
  rcases y with ⟨d, f⟩
  by_cases hcd : c = d
  · subst d
    have hef : e ≠ f := by
      intro hef
      subst f
      exact hxy rfl
    let R := D.cycleRecordAt c
    simpa [decompositionFourCycleEmbedding] using
      cycleResidualC4_pairwise_disjoint m c.1 (lt_trans c.2 hD)
        R.walk R.isCycle hef
  · exact (D.indexedCycleAugmentedGraph_pairwiseDisjoint m hD hcd).mono
      (decompositionResidualFour_le_indexedCycleAugmentedGraph m D hD ⟨c, e⟩)
      (decompositionResidualFour_le_indexedCycleAugmentedGraph m D hD ⟨d, f⟩)

lemma decompositionUnusedFour_disjoint_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    (x : DecompositionUnusedFourIndex m D)
    (y : DecompositionTriangleIndex D) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inr x)))
      ((SimpleGraph.cycleGraph 3).map
        (decompositionTriangleEmbedding m D hD y)) := by
  rcases x with ⟨e, t⟩
  rcases y with ⟨c, b⟩
  let R := D.cycleRecordAt c
  cases b
  · simpa [decompositionFourCycleEmbedding,
        decompositionTriangleEmbedding] using
      unusedPathC4_disjoint_lastCycleEndpointTriangle
        m D.cycleCount c.1 hD.le c.2 (lt_trans c.2 hD)
          e t R.walk R.isCycle
  · simpa [decompositionFourCycleEmbedding,
        decompositionTriangleEmbedding] using
      unusedPathC4_disjoint_firstCycleEndpointTriangle
        m D.cycleCount c.1 hD.le c.2 (lt_trans c.2 hD)
          e t R.walk R.isCycle

lemma decompositionUnusedFour_disjoint_fiveCycle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    (x : DecompositionUnusedFourIndex m D)
    (y : DecompositionFiveCycleIndex D) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inr x)))
      ((SimpleGraph.cycleGraph 5).map
        (decompositionFiveCycleEmbedding m D hD y)) := by
  rcases x with ⟨e, t⟩
  rcases y with ⟨c, i⟩
  let R := D.cycleRecordAt c
  simpa [decompositionFourCycleEmbedding,
      decompositionFiveCycleEmbedding] using
    unusedPathC4_disjoint_cycleChainC5
      m D.cycleCount c.1 hD.le c.2 (lt_trans c.2 hD)
        e t R.walk R.isCycle i

lemma decompositionResidualFour_disjoint_unusedFour
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    (x : DecompositionResidualFourIndex D)
    (y : DecompositionUnusedFourIndex m D) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inl x)))
      ((SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inr y))) := by
  rcases x with ⟨c, e⟩
  rcases y with ⟨f, t⟩
  let R := D.cycleRecordAt c
  simpa [decompositionFourCycleEmbedding] using
    cycleResidualC4_disjoint_unusedPathC4
      m D.cycleCount c.1 hD.le c.2 (lt_trans c.2 hD)
        R.walk R.isCycle e f t

lemma decompositionUnusedFour_pairwise_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2)
    {x y : DecompositionUnusedFourIndex m D} (hxy : x ≠ y) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inr x)))
      ((SimpleGraph.cycleGraph 4).map
        (decompositionFourCycleEmbedding m D hD (.inr y))) := by
  rcases x with ⟨e, t⟩
  rcases y with ⟨f, u⟩
  simpa [decompositionFourCycleEmbedding] using
    unusedPathC4_pairwise_disjoint m D.cycleCount hD.le hxy

/-- All short cycles produced by the recursive expansion are pairwise
edge-disjoint, including the four-cycles occupying the unused path slots. -/
lemma shortCycleFamily_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) :
    (D.shortCycleFamily m hD).PairwiseDisjoint := by
  intro x y hxy
  rcases x with x | (x | x)
  · rcases y with y | (y | y)
    · exact decompositionTriangle_pairwise_disjoint m D hD (by
        intro h
        exact hxy (by simp [h]))
    · rcases y with y | y
      · exact decompositionTriangle_disjoint_residualFour m D hD x y
      · exact (decompositionUnusedFour_disjoint_triangle m D hD y x).symm
    · exact decompositionTriangle_disjoint_fiveCycle m D hD x y
  · rcases x with x | x
    · rcases y with y | (y | y)
      · exact (decompositionTriangle_disjoint_residualFour m D hD y x).symm
      · rcases y with y | y
        · exact decompositionResidualFour_pairwise_disjoint m D hD (by
            intro h
            exact hxy (by simp [h]))
        · exact decompositionResidualFour_disjoint_unusedFour m D hD x y
      · exact (decompositionFiveCycle_disjoint_residualFour m D hD y x).symm
    · rcases y with y | (y | y)
      · exact decompositionUnusedFour_disjoint_triangle m D hD x y
      · rcases y with y | y
        · exact (decompositionResidualFour_disjoint_unusedFour m D hD y x).symm
        · exact decompositionUnusedFour_pairwise_disjoint m D hD (by
            intro h
            exact hxy (by simp [h]))
      · exact decompositionUnusedFour_disjoint_fiveCycle m D hD x y
  · rcases y with y | (y | y)
    · exact (decompositionTriangle_disjoint_fiveCycle m D hD y x).symm
    · rcases y with y | y
      · exact decompositionFiveCycle_disjoint_residualFour m D hD x y
      · exact (decompositionUnusedFour_disjoint_fiveCycle m D hD y x).symm
    · exact decompositionFiveCycle_pairwise_disjoint m D hD (by
        intro h
        exact hxy (by simp [h]))

@[simp]
lemma indexedCycleAugmentedGraph_step_last
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V}
    (m : ℕ) (p : G.Walk v v) (hp : p.IsCycle)
    (tail : CycleDecomposition (G \ p.toSubgraph.spanningCoe))
    (hD : (CycleDecomposition.step p hp tail).cycleCount < m ^ 2) :
    (CycleDecomposition.step p hp tail).indexedCycleAugmentedGraph m hD
        (Fin.last tail.cycleCount) =
      cycleAugmentedPieceGraph m tail.cycleCount (by
        simp only [cycleCount] at hD
        omega) p hp := by
  unfold indexedCycleAugmentedGraph
  rw [cycleRecordAt_step_last]
  simp only [Fin.val_last]

@[simp]
lemma indexedCycleAugmentedGraph_step_castSucc
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V}
    (m : ℕ) (p : G.Walk v v) (hp : p.IsCycle)
    (tail : CycleDecomposition (G \ p.toSubgraph.spanningCoe))
    (hD : (CycleDecomposition.step p hp tail).cycleCount < m ^ 2)
    (c : Fin tail.cycleCount) :
    (CycleDecomposition.step p hp tail).indexedCycleAugmentedGraph m hD
        c.castSucc =
      tail.indexedCycleAugmentedGraph m (by
        simp only [cycleCount] at hD
        omega) c := by
  unfold indexedCycleAugmentedGraph
  rw [cycleRecordAt_step_castSucc]
  simp only [Fin.val_castSucc]

lemma augmentedGraph_eq_graphSup_indexedCycles
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) :
    D.augmentedGraph m hD =
      graphSup univ (D.indexedCycleAugmentedGraph m hD) := by
  induction D with
  | empty =>
      rw [augmentedGraph]
      change (⊥ : SimpleGraph (PathCoverVertex V (6 * m ^ 2))) =
        graphSup (univ : Finset (Fin 0)) _
      rw [show (univ : Finset (Fin 0)) = ∅ by
        ext c
        exact Fin.elim0 c]
      exact (graphSup_empty _).symm
  | @step G v p hp tail ih =>
      have htail : tail.cycleCount < m ^ 2 := by
        simp only [cycleCount] at hD
        omega
      rw [augmentedGraph, ih htail]
      unfold graphSup
      simp_rw [Finset.sup_univ_eq_iSup]
      ext a b
      simp only [SimpleGraph.sup_adj, SimpleGraph.iSup_adj]
      constructor
      · rintro (⟨c, hc⟩ | hc)
        · exact ⟨c.castSucc, by
            simpa only [indexedCycleAugmentedGraph_step_castSucc] using hc⟩
        · exact ⟨Fin.last tail.cycleCount, by
            simpa only [indexedCycleAugmentedGraph_step_last] using hc⟩
      · rintro ⟨c, hc⟩
        cases c using Fin.lastCases with
        | last =>
            right
            simpa only [indexedCycleAugmentedGraph_step_last] using hc
        | cast c =>
            left
            exact ⟨c, by
              simpa only [indexedCycleAugmentedGraph_step_castSucc] using hc⟩

lemma indexedCycleAugmentedGraph_eq_component_iSups
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) (c : Fin D.cycleCount) :
    D.indexedCycleAugmentedGraph m hD c =
      (⨆ b : Bool,
        (SimpleGraph.cycleGraph 3).map
          (decompositionTriangleEmbedding m D hD ⟨c, b⟩)) ⊔
      ((⨆ i : Fin ((D.cycleRecordAt c).walk.length - 2),
          (SimpleGraph.cycleGraph 5).map
            (decompositionFiveCycleEmbedding m D hD ⟨c, i⟩)) ⊔
        ⨆ e : CycleResidualEdge (D.cycleRecordAt c).walk
            (D.cycleRecordAt c).isCycle,
          (SimpleGraph.cycleGraph 4).map
            (decompositionFourCycleEmbedding m D hD (.inl ⟨c, e⟩))) := by
  let R := D.cycleRecordAt c
  unfold indexedCycleAugmentedGraph cycleAugmentedPieceGraph
    cycleShortPieceGraph cycleResidualGraph decompositionTriangleEmbedding
    decompositionFiveCycleEmbedding decompositionFourCycleEmbedding
  rw [iSup_bool_eq]
  simp
  ac_rfl

lemma iSup_indexedCycleAugmentedGraph_eq_components
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) :
    (⨆ c : Fin D.cycleCount,
        D.indexedCycleAugmentedGraph m hD c) =
      (⨆ c : Fin D.cycleCount, ⨆ b : Bool,
        (SimpleGraph.cycleGraph 3).map
          (decompositionTriangleEmbedding m D hD ⟨c, b⟩)) ⊔
      ((⨆ c : Fin D.cycleCount,
          ⨆ e : CycleResidualEdge (D.cycleRecordAt c).walk
              (D.cycleRecordAt c).isCycle,
            (SimpleGraph.cycleGraph 4).map
              (decompositionFourCycleEmbedding m D hD (.inl ⟨c, e⟩))) ⊔
        ⨆ c : Fin D.cycleCount,
          ⨆ i : Fin ((D.cycleRecordAt c).walk.length - 2),
            (SimpleGraph.cycleGraph 5).map
              (decompositionFiveCycleEmbedding m D hD ⟨c, i⟩)) := by
  apply le_antisymm
  · refine iSup_le fun c => ?_
    rw [indexedCycleAugmentedGraph_eq_component_iSups]
    refine sup_le (le_sup_of_le_left (le_iSup
      (fun d : Fin D.cycleCount => ⨆ b : Bool,
        (SimpleGraph.cycleGraph 3).map
          (decompositionTriangleEmbedding m D hD ⟨d, b⟩)) c)) (sup_le ?_ ?_)
    · exact le_sup_of_le_right (le_sup_of_le_right (le_iSup
        (fun d : Fin D.cycleCount =>
          ⨆ i : Fin ((D.cycleRecordAt d).walk.length - 2),
            (SimpleGraph.cycleGraph 5).map
              (decompositionFiveCycleEmbedding m D hD ⟨d, i⟩)) c))
    · exact le_sup_of_le_right (le_sup_of_le_left (le_iSup
        (fun d : Fin D.cycleCount =>
          ⨆ e : CycleResidualEdge (D.cycleRecordAt d).walk
              (D.cycleRecordAt d).isCycle,
            (SimpleGraph.cycleGraph 4).map
              (decompositionFourCycleEmbedding m D hD (.inl ⟨d, e⟩))) c))
  · refine sup_le ?_ (sup_le ?_ ?_)
    · refine iSup_le fun c => le_iSup_of_le c ?_
      rw [indexedCycleAugmentedGraph_eq_component_iSups]
      exact le_sup_left
    · refine iSup_le fun c => le_iSup_of_le c ?_
      rw [indexedCycleAugmentedGraph_eq_component_iSups]
      exact le_sup_of_le_right le_sup_right
    · refine iSup_le fun c => le_iSup_of_le c ?_
      rw [indexedCycleAugmentedGraph_eq_component_iSups]
      exact le_sup_of_le_right le_sup_left

/-- The graph supremum of the concrete short-cycle family is exactly the
completed augmented graph. -/
lemma graphSup_shortCycleFamily_eq_completedAugmentedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) :
    graphSup univ (D.shortCycleFamily m hD).graph =
      D.completedAugmentedGraph m hD := by
  classical
  unfold graphSup
  rw [Finset.sup_univ_eq_iSup, iSup_sum, iSup_sum, iSup_sum,
    iSup_sigma, iSup_sigma, iSup_prod, iSup_sigma]
  simp only [shortCycleFamily, ShortCycleFamily.graph]
  rw [completedAugmentedGraph,
    augmentedGraph_eq_graphSup_indexedCycles]
  unfold graphSup unusedPathGraph
  rw [Finset.sup_univ_eq_iSup,
    iSup_indexedCycleAugmentedGraph_eq_components]
  ac_rfl

/-- Instance-independent version of the exact short-cycle coverage identity. -/
lemma iSup_shortCycleFamily_eq_completedAugmentedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) :
    (⨆ i, (D.shortCycleFamily m hD).graph i) =
      D.completedAugmentedGraph m hD := by
  calc
    (⨆ i, (D.shortCycleFamily m hD).graph i) =
        graphSup univ (D.shortCycleFamily m hD).graph := by
      unfold graphSup
      rw [Finset.sup_univ_eq_iSup]
    _ = D.completedAugmentedGraph m hD :=
      graphSup_shortCycleFamily_eq_completedAugmentedGraph m D hD

end CycleDecomposition

end

end Erdos207
