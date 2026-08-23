/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.CycleAugmentation

/-!
# Augmenting every cycle in a cycle decomposition

This file assembles the exact one-cycle identity proved in
`CycleAugmentation`.  Cycle number `c` consumes universal path-cover slots
`2c` and `2c+1`.  Recursing through a `CycleDecomposition` therefore covers
exactly the embedded original graph and precisely the first two slots for
each cycle; the remaining slots are handled by `unusedPathGraph`.
-/

namespace Erdos207

noncomputable section

/-- The union of the two path-cover slots allocated to each cycle number
strictly below `r`. -/
def usedPathSlotGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (m r : ℕ) (hr : r ≤ m ^ 2) :
    SimpleGraph (PathCoverVertex V (6 * m ^ 2)) :=
  (⨆ c : Fin r,
      pathCoverSlotGraph (V := V)
        (firstCyclePathSlot m c.1 (lt_of_lt_of_le c.2 hr))) ⊔
    ⨆ c : Fin r,
      pathCoverSlotGraph (V := V)
        (secondCyclePathSlot m c.1 (lt_of_lt_of_le c.2 hr))

/-- Split a supremum over `Fin (r + 1)` into its first `r` terms and its
last term. -/
lemma iSup_fin_succ_eq_init_sup_last
    {X : Type*} (r : ℕ) (F : Fin (r + 1) → SimpleGraph X) :
    (⨆ i, F i) =
      (⨆ i : Fin r, F ⟨i.1, Nat.lt_succ_of_lt i.2⟩) ⊔ F ⟨r, by omega⟩ := by
  ext u v
  simp only [SimpleGraph.iSup_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hir : i.1 < r
    · left
      exact ⟨⟨i.1, hir⟩, by simpa using hi⟩
    · right
      have hval : i.1 = r := by omega
      have hieq : i = ⟨r, by omega⟩ := Fin.ext hval
      simpa only [hieq] using hi
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨⟨i.1, by omega⟩, hi⟩
    · exact ⟨⟨r, by omega⟩, hi⟩

lemma usedPathSlotGraph_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (m r : ℕ) (hr : r + 1 ≤ m ^ 2) :
    usedPathSlotGraph (V := V) m (r + 1) hr =
      usedPathSlotGraph (V := V) m r (by omega) ⊔
        (pathCoverSlotGraph
            (firstCyclePathSlot m r (by omega)) ⊔
          pathCoverSlotGraph
            (secondCyclePathSlot m r (by omega))) := by
  ext u v
  simp only [usedPathSlotGraph, SimpleGraph.sup_adj, SimpleGraph.iSup_adj]
  constructor
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · by_cases hcr : c.1 < r
      · left; left
        exact ⟨⟨c.1, hcr⟩, by simpa using hc⟩
      · right; left
        have hval : c.1 = r := by omega
        have heq : c = ⟨r, by omega⟩ := Fin.ext hval
        simpa only [heq] using hc
    · by_cases hcr : c.1 < r
      · left; right
        exact ⟨⟨c.1, hcr⟩, by simpa using hc⟩
      · right; right
        have hval : c.1 = r := by omega
        have heq : c = ⟨r, by omega⟩ := Fin.ext hval
        simpa only [heq] using hc
  · rintro ((⟨c, hc⟩ | ⟨c, hc⟩) | hc | hc)
    · left
      exact ⟨⟨c.1, by omega⟩, by simpa using hc⟩
    · right
      exact ⟨⟨c.1, by omega⟩, by simpa using hc⟩
    · left
      exact ⟨⟨r, by omega⟩, by simpa using hc⟩
    · right
      exact ⟨⟨r, by omega⟩, by simpa using hc⟩

/-- The slots used by the cycle decomposition together with the canonically
paired unused slots exhaust the entire universal path cover. -/
lemma usedPathSlotGraph_sup_unusedPathGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (m r : ℕ) (hr : r ≤ m ^ 2) :
    usedPathSlotGraph (V := V) m r hr ⊔
        unusedPathGraph (V := V) m r hr =
      pathCoverGraph V (6 * m ^ 2) := by
  rw [pathCoverGraph_eq_iSup_pathCoverSlotGraph,
    iSup_pathSlots_eq_used_sup_unused m r hr,
    ← unusedPathGraph_eq_slotGraphs]
  rfl

namespace CycleDecomposition

/-- The union of all augmented cycle pieces in a recursive cycle
decomposition.  The current cycle is numbered after all cycles in the tail,
so the indices are exactly `0, ..., cycleCount - 1`. -/
def augmentedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) :
    SimpleGraph (PathCoverVertex V (6 * m ^ 2)) :=
  match D with
  | .empty => ⊥
  | .step p hp tail =>
      augmentedGraph m tail (by
        simp only [cycleCount] at hD
        omega) ⊔
        cycleAugmentedPieceGraph m tail.cycleCount (by
          simp only [cycleCount] at hD
          omega) p hp

/-- Mapping the canonical cycle copy into root vertices is the same as
mapping the walk's exact spanning graph into root vertices. -/
lemma map_walkCyclePathRootEmbedding_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V} {k : ℕ}
    (p : G.Walk v v) (hp : p.IsCycle) :
    (SimpleGraph.cycleGraph p.length).map
        (walkCyclePathRootEmbedding (k := k) p hp) =
      p.toSubgraph.spanningCoe.map
        (pathCoverRootEmbedding (X := V) (k := k)) := by
  rw [← walkCycleGraph_map_eq_spanningCoe p hp,
    SimpleGraph.map_map]
  rfl

/-- Exact coverage by all augmented cycle pieces: they contain every root
edge of the decomposed graph and exactly the two universal path-cover slots
assigned to each decomposition cycle. -/
lemma augmentedGraph_eq_root_sup_usedSlots
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) :
    D.augmentedGraph m hD =
      G.map (pathCoverRootEmbedding
          (X := V) (k := 6 * m ^ 2)) ⊔
        usedPathSlotGraph (V := V) m D.cycleCount hD.le := by
  induction D with
  | empty =>
      ext u v
      simp [augmentedGraph, usedPathSlotGraph, cycleCount]
  | @step G v p hp tail ih =>
      have htail : tail.cycleCount < m ^ 2 := by
        simp only [cycleCount] at hD
        omega
      have hsucc : tail.cycleCount + 1 ≤ m ^ 2 := by
        simp only [cycleCount] at hD
        omega
      rw [augmentedGraph, ih htail,
        cycleAugmentedPieceGraph_eq,
        map_walkCyclePathRootEmbedding_eq]
      simp only [cycleCount]
      rw [usedPathSlotGraph_succ m tail.cycleCount hsucc]
      have hroot :
          (G \ p.toSubgraph.spanningCoe).map
                (pathCoverRootEmbedding
                  (X := V) (k := 6 * m ^ 2)) ⊔
              p.toSubgraph.spanningCoe.map
                (pathCoverRootEmbedding
                  (X := V) (k := 6 * m ^ 2)) =
            G.map (pathCoverRootEmbedding
              (X := V) (k := 6 * m ^ 2)) := by
        rw [← SimpleGraph.map_sup_function,
          sdiff_sup_cancel (walkSpanningCoe_le p)]
      rw [← hroot]
      ac_rfl

/-- Add the paired four-cycles made from all path-cover slots that were not
used by a decomposition cycle.  This is the complete short-cycle expansion
of the original even graph plus the universal path cover. -/
def completedAugmentedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) :
    SimpleGraph (PathCoverVertex V (6 * m ^ 2)) :=
  D.augmentedGraph m hD ⊔
    unusedPathGraph (V := V) m D.cycleCount hD.le

/-- Exact global coverage identity for the cycle/path-cover expansion. -/
lemma completedAugmentedGraph_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G)
    (hD : D.cycleCount < m ^ 2) :
    D.completedAugmentedGraph m hD =
      G.map (pathCoverRootEmbedding
          (X := V) (k := 6 * m ^ 2)) ⊔
        pathCoverGraph V (6 * m ^ 2) := by
  unfold completedAugmentedGraph
  rw [augmentedGraph_eq_root_sup_usedSlots]
  rw [sup_assoc,
    usedPathSlotGraph_sup_unusedPathGraph m D.cycleCount hD.le]

end CycleDecomposition

end


end Erdos207
