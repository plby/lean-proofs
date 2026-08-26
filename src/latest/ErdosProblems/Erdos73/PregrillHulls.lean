/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.FullPregrill
import ErdosProblems.Erdos73.RootedPartition

/-!
# Filling the row segments inside full pregrill columns

Each column is enlarged by the closed first-to-last-hit segment of each
row. The enlarged columns remain connected and pairwise disjoint.
-/

namespace Erdos73Infrastructure.SimpleGraph.FullPregrill
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} {G : _root_.SimpleGraph V} {m n : ℕ}

def first (P : FullPregrill G m n) (r : Fin m) (j : Fin n) : V :=
  (P.row r).firstHitVertex (P.column j) (P.meets r j)

def last (P : FullPregrill G m n) (r : Fin m) (j : Fin n) : V :=
  (P.row r).lastHitVertex (P.column j) (P.meets r j)

theorem first_mem_row (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    P.first r j ∈ (P.row r).vertexSet := (P.row r).firstHitVertex_mem_vertexSet _ _

theorem first_mem_column (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    P.first r j ∈ P.column j := (P.row r).firstHitVertex_mem_set _ _

theorem last_mem_row (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    P.last r j ∈ (P.row r).vertexSet := (P.row r).lastHitVertex_mem_vertexSet _ _

theorem last_mem_column (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    P.last r j ∈ P.column j := (P.row r).lastHitVertex_mem_set _ _

theorem first_before_of_mem (P : FullPregrill G m n) (r : Fin m) (j : Fin n)
    {v : V} (hvrow : v ∈ (P.row r).vertexSet) (hvcol : v ∈ P.column j) :
    (P.row r).Before (P.first r j) v :=
  (P.row r).firstHitVertex_before_of_mem_set _ _ hvrow hvcol

theorem before_last_of_mem (P : FullPregrill G m n) (r : Fin m) (j : Fin n)
    {v : V} (hvrow : v ∈ (P.row r).vertexSet) (hvcol : v ∈ P.column j) :
    (P.row r).Before v (P.last r j) :=
  (P.row r).before_lastHitVertex_of_mem_set _ _ hvrow hvcol

theorem first_before_last (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    (P.row r).Before (P.first r j) (P.last r j) :=
  P.first_before_of_mem r j (P.last_mem_row r j) (P.last_mem_column r j)

def rowHull (P : FullPregrill G m n) (r : Fin m) (j : Fin n) : GraphPath G :=
  (P.row r).segmentOfBefore (P.first_before_last r j)

@[simp] theorem rowHull_source (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    (P.rowHull r j).source = P.first r j := rfl

@[simp] theorem rowHull_target (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    (P.rowHull r j).target = P.last r j := rfl

theorem rowHull_subset_row (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    (P.rowHull r j).vertexSet ⊆ (P.row r).vertexSet :=
  (P.row r).segmentOfBefore_vertexSet_subset _

theorem first_mem_rowHull (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    P.first r j ∈ (P.rowHull r j).vertexSet := (P.rowHull r j).source_mem_vertexSet

theorem last_mem_rowHull (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    P.last r j ∈ (P.rowHull r j).vertexSet := (P.rowHull r j).target_mem_vertexSet

theorem first_before_of_mem_rowHull (P : FullPregrill G m n) (r : Fin m) (j : Fin n)
    {v : V} (hv : v ∈ (P.rowHull r j).vertexSet) : (P.row r).Before (P.first r j) v :=
  (P.row r).before_of_mem_segmentOfBefore_left _ hv

theorem before_last_of_mem_rowHull (P : FullPregrill G m n) (r : Fin m) (j : Fin n)
    {v : V} (hv : v ∈ (P.rowHull r j).vertexSet) : (P.row r).Before v (P.last r j) :=
  (P.row r).before_of_mem_segmentOfBefore_right _ hv

theorem row_inter_column_subset_rowHull (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    (P.row r).vertexSet ∩ P.column j ⊆ (P.rowHull r j).vertexSet := by
  intro v hv
  obtain ⟨hvrow, hvcol⟩ := Finset.mem_inter.mp hv
  exact (P.row r).mem_segmentOfBefore_of_before_of_before (P.first_before_last r j)
    (P.first_before_of_mem r j hvrow hvcol) (P.before_last_of_mem r j hvrow hvcol)

theorem last_before_first_of_lt (P : FullPregrill G m n) (r : Fin m)
    {i j : Fin n} (hij : i < j) : (P.row r).Before (P.last r i) (P.first r j) :=
  P.ordered i j hij r _ (P.last_mem_column r i) (P.last_mem_row r i)
    _ (P.first_mem_column r j) (P.first_mem_row r j)

theorem last_ne_first_of_ne (P : FullPregrill G m n) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) : P.last r i ≠ P.first r j := by
  intro h
  exact Finset.disjoint_left.mp (P.column_disjoint hij) (P.last_mem_column r i)
    (h ▸ P.first_mem_column r j)

theorem rowHull_disjoint_column (P : FullPregrill G m n) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) : Disjoint (P.rowHull r i).vertexSet (P.column j) := by
  apply Finset.disjoint_left.mpr
  intro v hvH hvQ
  have hvrow := P.rowHull_subset_row r i hvH
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hbv := P.ordered i j hlt r _ (P.last_mem_column r i) (P.last_mem_row r i)
      v hvQ hvrow
    have heq : v = P.last r i := (P.row r).before_antisymm
      (P.before_last_of_mem_rowHull r i hvH) hbv
    exact Finset.disjoint_left.mp (P.column_disjoint hij) (heq ▸ P.last_mem_column r i) hvQ
  · have hva := P.ordered j i hgt r v hvQ hvrow
      _ (P.first_mem_column r i) (P.first_mem_row r i)
    have heq : v = P.first r i := (P.row r).before_antisymm hva
      (P.first_before_of_mem_rowHull r i hvH)
    exact Finset.disjoint_left.mp (P.column_disjoint hij) (heq ▸ P.first_mem_column r i) hvQ

theorem rowHull_disjoint_rowHull (P : FullPregrill G m n) (r s : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    Disjoint (P.rowHull r i).vertexSet (P.rowHull s j).vertexSet := by
  by_cases hrs : r = s
  · subst s
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (P.row r).segmentOfBefore_disjoint_of_strict_target_before_source
        (P.first_before_last r i) (P.first_before_last r j)
        (P.last_before_first_of_lt r hlt) (P.last_ne_first_of_ne r hij)
    · exact ((P.row r).segmentOfBefore_disjoint_of_strict_target_before_source
        (P.first_before_last r j) (P.first_before_last r i)
        (P.last_before_first_of_lt r hgt) (P.last_ne_first_of_ne r hij.symm)).symm
  · exact (P.row_disjoint hrs).mono (P.rowHull_subset_row r i) (P.rowHull_subset_row s j)

def expandedColumn (P : FullPregrill G m n) (j : Fin n) : Finset V :=
  P.column j ∪ Finset.univ.biUnion fun r ↦ (P.rowHull r j).vertexSet

theorem column_subset_expandedColumn (P : FullPregrill G m n) (j : Fin n) :
    P.column j ⊆ P.expandedColumn j := Finset.subset_union_left

theorem rowHull_subset_expandedColumn (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    (P.rowHull r j).vertexSet ⊆ P.expandedColumn j := by
  intro v hv
  exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, hv⟩))

theorem expandedColumn_disjoint (P : FullPregrill G m n) :
    Pairwise fun i j ↦ Disjoint (P.expandedColumn i) (P.expandedColumn j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  rcases Finset.mem_union.mp hvi with hviQ | hviH
  · rcases Finset.mem_union.mp hvj with hvjQ | hvjH
    · exact Finset.disjoint_left.mp (P.column_disjoint hij) hviQ hvjQ
    · obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hvjH
      exact Finset.disjoint_left.mp (P.rowHull_disjoint_column r hij.symm) hr hviQ
  · obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hviH
    rcases Finset.mem_union.mp hvj with hvjQ | hvjH
    · exact Finset.disjoint_left.mp (P.rowHull_disjoint_column r hij) hr hvjQ
    · obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp hvjH
      exact Finset.disjoint_left.mp (P.rowHull_disjoint_rowHull r s hij) hr hs

theorem expandedColumn_connected (P : FullPregrill G m n) (j : Fin n) :
    (G.induce (P.expandedColumn j : Set V)).Connected := by
  have hconn (S : Finset (Fin m)) :
      (G.induce (↑(P.column j ∪ S.biUnion fun r ↦ (P.rowHull r j).vertexSet) : Set V)).Connected := by
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.biUnion_empty, Finset.union_empty]
      exact P.connected j
    | @insert r S hr ih =>
      have heq : P.column j ∪ (insert r S).biUnion (fun s ↦ (P.rowHull s j).vertexSet) =
          (P.column j ∪ S.biUnion (fun s ↦ (P.rowHull s j).vertexSet)) ∪
            (P.rowHull r j).vertexSet := by
        rw [Finset.biUnion_insert]
        ac_rfl
      rw [heq, Finset.coe_union]
      exact _root_.SimpleGraph.induce_union_connected ih.preconnected
        (P.rowHull r j).connected_induce_vertexSet.preconnected
        ⟨P.first r j, Finset.mem_union.mpr (Or.inl (P.first_mem_column r j)),
          P.first_mem_rowHull r j⟩
  exact hconn Finset.univ

/-- Enlarging a column introduces precisely its closed row hull on any
particular row, and no further vertices of that row. -/
theorem row_inter_expandedColumn_eq_rowHull (P : FullPregrill G m n) (r : Fin m) (j : Fin n) :
    (P.row r).vertexSet ∩ P.expandedColumn j = (P.rowHull r j).vertexSet := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨hvrow, hvcol⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_union.mp hvcol with hvQ | hvH
    · exact P.row_inter_column_subset_rowHull r j (Finset.mem_inter.mpr ⟨hvrow, hvQ⟩)
    · obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp hvH
      by_cases hrs : r = s
      · subst s
        exact hs
      · exact (Finset.disjoint_left.mp (P.row_disjoint hrs) hvrow
          (P.rowHull_subset_row s j hs)).elim
  · intro v hv
    exact Finset.mem_inter.mpr ⟨P.rowHull_subset_row r j hv,
      P.rowHull_subset_expandedColumn r j hv⟩

theorem expandedColumn_ordered (P : FullPregrill G m n)
    {i j : Fin n} (hij : i < j) (r : Fin m)
    {x y : V} (hxi : x ∈ P.expandedColumn i) (hxr : x ∈ (P.row r).vertexSet)
    (hyj : y ∈ P.expandedColumn j) (hyr : y ∈ (P.row r).vertexSet) :
    (P.row r).Before x y := by
  have hxH : x ∈ (P.rowHull r i).vertexSet := by
    rw [← P.row_inter_expandedColumn_eq_rowHull r i]
    exact Finset.mem_inter.mpr ⟨hxr, hxi⟩
  have hyH : y ∈ (P.rowHull r j).vertexSet := by
    rw [← P.row_inter_expandedColumn_eq_rowHull r j]
    exact Finset.mem_inter.mpr ⟨hyr, hyj⟩
  exact (P.row r).before_trans (P.before_last_of_mem_rowHull r i hxH)
    ((P.row r).before_trans (P.last_before_first_of_lt r hij)
      (P.first_before_of_mem_rowHull r j hyH))

/-- Partition an expanded column without splitting any row hull. The
quotient column graph is connected and all parts stay in this column. -/
theorem exists_column_partition [Fintype V]
    (P : FullPregrill G m n) (hm : 0 < m) (j : Fin n) :
    ∃ B : Fin m → Finset V,
      (∀ r, (P.rowHull r j).vertexSet ⊆ B r ∧ B r ⊆ P.expandedColumn j ∧
        (G.induce (B r : Set V)).Connected) ∧
      (Pairwise fun r s ↦ Disjoint (B r) (B s)) ∧
      (∀ v ∈ P.expandedColumn j, ∃ r, v ∈ B r) ∧
      (Erdos73.connectedPartitionGraph G B).Connected := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hinit (r : Fin m) : (P.rowHull r j).vertexSet.Nonempty ∧
      (G.induce ((P.rowHull r j).vertexSet : Set V)).Connected :=
    ⟨⟨P.first r j, P.first_mem_rowHull r j⟩, (P.rowHull r j).connected_induce_vertexSet⟩
  have hdisj : Pairwise fun r s ↦ Disjoint (P.rowHull r j).vertexSet (P.rowHull s j).vertexSet :=
    fun r s hrs ↦ (P.row_disjoint hrs).mono (P.rowHull_subset_row r j) (P.rowHull_subset_row s j)
  obtain ⟨B, hB, hd, hc⟩ := Erdos73.exists_connected_partition_inside
    (P.expandedColumn j) (P.expandedColumn_connected j)
    (fun r ↦ (P.rowHull r j).vertexSet) hinit
    (fun r ↦ P.rowHull_subset_expandedColumn r j) hdisj
  refine ⟨B, hB, hd, hc, ?_⟩
  exact Erdos73.connectedPartitionGraph_connected_on (P.expandedColumn j)
    (P.expandedColumn_connected j) (fun r ↦ P.first r j) B
    (fun r ↦ (hB r).1 (P.first_mem_rowHull r j)) (fun r ↦ (hB r).2.1) hd hc

end
end Erdos73Infrastructure.SimpleGraph.FullPregrill
