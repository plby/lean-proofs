/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.PregrillConnectors
import ErdosProblems.Erdos73.GrillColumns

/-!
# Assembling ordinary grill minor branch sets from a full pregrill
-/

namespace Erdos73Infrastructure.SimpleGraph.FullPregrill
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} {G : _root_.SimpleGraph V} {m n : ℕ}

/-- Attach the half-open connector to the next column, or the already
contained row hull when this is the last column. -/
def attachment (P : FullPregrill G m (n + 1)) (r : Fin m) (j : Fin (n + 1)) : GraphPath G :=
  if h : j.val < n then (P.connector r ⟨j.val, h⟩).dropLast else P.rowHull r j

theorem attachment_subset_row (P : FullPregrill G m (n + 1)) (r : Fin m) (j : Fin (n + 1)) :
    (P.attachment r j).vertexSet ⊆ (P.row r).vertexSet := by
  unfold attachment
  split
  · exact GraphPath.dropLast_vertexSet_subset _ |>.trans (P.connector_subset_row r _)
  · exact P.rowHull_subset_row r j

theorem attachment_meets_expandedColumn
    (P : FullPregrill G m (n + 1)) (r : Fin m) (j : Fin (n + 1))
    {k : Fin (n + 1)} {v : V}
    (hvA : v ∈ (P.attachment r j).vertexSet) (hvK : v ∈ P.expandedColumn k) :
    k = j ∧ v ∈ (P.rowHull r j).vertexSet := by
  by_cases hj : j.val < n
  · rw [attachment, dif_pos hj] at hvA
    obtain ⟨hk, hv⟩ := P.connector_dropLast_meets_column r ⟨j.val, hj⟩ hvA hvK
    have heq : (⟨j.val, hj⟩ : Fin n).castSucc = j := Fin.ext rfl
    rw [heq] at hk hv
    exact ⟨hk, hv ▸ P.last_mem_rowHull r j⟩
  · rw [attachment, dif_neg hj] at hvA
    have hk : k = j := by
      by_contra h
      exact Finset.disjoint_left.mp (P.expandedColumn_disjoint h) hvK
        (P.rowHull_subset_expandedColumn r j hvA)
    exact ⟨hk, hvA⟩

theorem attachment_source_mem_rowHull
    (P : FullPregrill G m (n + 1)) (r : Fin m) (j : Fin (n + 1)) :
    (P.attachment r j).source ∈ (P.rowHull r j).vertexSet := by
  by_cases hj : j.val < n
  · rw [attachment, dif_pos hj, GraphPath.dropLast_source, connector_source]
    have heq : (⟨j.val, hj⟩ : Fin n).castSucc = j := Fin.ext rfl
    rw [heq]
    exact P.last_mem_rowHull r j
  · rw [attachment, dif_neg hj]
    exact (P.rowHull r j).source_mem_vertexSet

theorem attachment_disjoint (P : FullPregrill G m (n + 1)) :
    Pairwise fun x y : Fin m × Fin (n + 1) ↦
      Disjoint (P.attachment x.1 x.2).vertexSet (P.attachment y.1 y.2).vertexSet := by
  intro x y hxy
  by_cases hr : x.1 = y.1
  · have hc : x.2 ≠ y.2 := fun h ↦ hxy (Prod.ext hr h)
    by_cases hx : x.2.val < n
    · by_cases hy : y.2.val < n
      · rw [attachment, dif_pos hx, attachment, dif_pos hy, ← hr]
        apply P.connector_dropLast_disjoint
        intro heq
        have heqval := congrArg (fun z : Fin m × Fin n ↦ z.2.val) heq
        exact hc (Fin.ext heqval)
      · apply Finset.disjoint_left.mpr
        intro v hvx hvy
        rw [attachment, dif_neg hy] at hvy
        exact hc (P.attachment_meets_expandedColumn x.1 x.2 hvx
          (P.rowHull_subset_expandedColumn y.1 y.2 hvy)).1.symm
    · apply Finset.disjoint_left.mpr
      intro v hvx hvy
      rw [attachment, dif_neg hx] at hvx
      exact hc (P.attachment_meets_expandedColumn y.1 y.2 hvy
        (P.rowHull_subset_expandedColumn x.1 x.2 hvx)).1
  · exact (P.row_disjoint hr).mono (P.attachment_subset_row x.1 x.2)
      (P.attachment_subset_row y.1 y.2)

/-- Actual connected parts of each expanded column, retaining every
row hull and inducing a connected quotient column graph. -/
structure ColumnPartitions (P : FullPregrill G m (n + 1)) where
  branch : Fin (n + 1) → Fin m → Finset V
  hull_subset : ∀ j r, (P.rowHull r j).vertexSet ⊆ branch j r
  subset_column : ∀ j r, branch j r ⊆ P.expandedColumn j
  connected : ∀ j r, (G.induce (branch j r : Set V)).Connected
  disjoint : ∀ j, Pairwise fun r s ↦ Disjoint (branch j r) (branch j s)
  quotient_connected : ∀ j, (Erdos73.connectedPartitionGraph G (branch j)).Connected

def chooseColumnPartitions [Fintype V] (P : FullPregrill G m (n + 1)) (hm : 0 < m) :
    ColumnPartitions P := by
  choose B hB hd hc hH using fun j ↦ P.exists_column_partition hm j
  exact {
    branch := B
    hull_subset := fun j r ↦ (hB j r).1
    subset_column := fun j r ↦ (hB j r).2.1
    connected := fun j r ↦ (hB j r).2.2
    disjoint := hd
    quotient_connected := hH }

namespace ColumnPartitions

variable {P : FullPregrill G m (n + 1)}

theorem branch_disjoint (C : ColumnPartitions P) :
    Pairwise fun x y : Fin m × Fin (n + 1) ↦ Disjoint (C.branch x.2 x.1) (C.branch y.2 y.1) := by
  intro x y hxy
  by_cases hc : x.2 = y.2
  · have hr : x.1 ≠ y.1 := fun h ↦ hxy (Prod.ext h hc)
    rw [← hc]
    exact C.disjoint x.2 hr
  · exact (P.expandedColumn_disjoint hc).mono (C.subset_column x.2 x.1) (C.subset_column y.2 y.1)

theorem attachment_disjoint_branch (C : ColumnPartitions P)
    {x y : Fin m × Fin (n + 1)} (hxy : x ≠ y) :
    Disjoint (P.attachment x.1 x.2).vertexSet (C.branch y.2 y.1) := by
  apply Finset.disjoint_left.mpr
  intro v hvA hvB
  obtain ⟨hcol, hvH⟩ := P.attachment_meets_expandedColumn x.1 x.2 hvA
    (C.subset_column y.2 y.1 hvB)
  exact Finset.disjoint_left.mp (C.branch_disjoint hxy) (C.hull_subset x.2 x.1 hvH) hvB

def extendedBranch (C : ColumnPartitions P) (x : Fin m × Fin (n + 1)) : Finset V :=
  C.branch x.2 x.1 ∪ (P.attachment x.1 x.2).vertexSet

theorem extendedBranch_connected (C : ColumnPartitions P) (x : Fin m × Fin (n + 1)) :
    (G.induce (C.extendedBranch x : Set V)).Connected := by
  rw [extendedBranch, Finset.coe_union]
  exact _root_.SimpleGraph.induce_union_connected (C.connected x.2 x.1).preconnected
    (P.attachment x.1 x.2).connected_induce_vertexSet.preconnected
    ⟨(P.attachment x.1 x.2).source,
      C.hull_subset x.2 x.1 (P.attachment_source_mem_rowHull x.1 x.2),
      (P.attachment x.1 x.2).source_mem_vertexSet⟩

theorem extendedBranch_disjoint (C : ColumnPartitions P) : Pairwise fun x y ↦
    Disjoint (C.extendedBranch x) (C.extendedBranch y) := by
  intro x y hxy
  exact Finset.disjoint_union_left.mpr ⟨
    Finset.disjoint_union_right.mpr ⟨C.branch_disjoint hxy, (C.attachment_disjoint_branch hxy.symm).symm⟩,
    Finset.disjoint_union_right.mpr ⟨C.attachment_disjoint_branch hxy, P.attachment_disjoint hxy⟩⟩

/-- The assembled labelled grill has each actual quotient column graph
and exactly the required horizontal path edges. -/
def grillGraph (C : ColumnPartitions P) : _root_.SimpleGraph (Fin m × Fin (n + 1)) where
  Adj x y :=
    (x.2 = y.2 ∧ (Erdos73.connectedPartitionGraph G (C.branch x.2)).Adj x.1 y.1) ∨
      (x.1 = y.1 ∧ (_root_.SimpleGraph.pathGraph (n + 1)).Adj x.2 y.2)
  symm := ⟨by
    rintro x y (⟨hc, h⟩ | ⟨hr, h⟩)
    · left
      refine ⟨hc.symm, ?_⟩
      rw [← hc]
      exact h.symm
    · exact Or.inr ⟨hr.symm, h.symm⟩⟩
  loopless := ⟨by
    rintro x (⟨_, h⟩ | ⟨_, h⟩)
    · exact (Erdos73.connectedPartitionGraph G (C.branch x.2)).irrefl h
    · exact (_root_.SimpleGraph.pathGraph (n + 1)).irrefl h⟩

theorem grillGraph_isGrill (C : ColumnPartitions P) : Erdos73.IsGrill C.grillGraph := by
  constructor
  · intro r s t hst
    exact Or.inr ⟨rfl, hst⟩
  · intro j
    have heq : Erdos73.grillColumnGraph C.grillGraph j =
        Erdos73.connectedPartitionGraph G (C.branch j) := by
      ext r s
      change (j = j ∧ (Erdos73.connectedPartitionGraph G (C.branch j)).Adj r s) ∨
        (r = s ∧ (_root_.SimpleGraph.pathGraph (n + 1)).Adj j j) ↔
          (Erdos73.connectedPartitionGraph G (C.branch j)).Adj r s
      simp only [true_and, _root_.SimpleGraph.irrefl, and_false, or_false]
    rw [heq]
    exact C.quotient_connected j

theorem extendedBranch_horizontal (C : ColumnPartitions P)
    (r : Fin m) (j k : Fin (n + 1)) (hjk : j.val + 1 = k.val) :
    ∃ x ∈ C.extendedBranch (r, j), ∃ y ∈ C.extendedBranch (r, k), G.Adj x y := by
  have hj : j.val < n := by omega
  let i : Fin n := ⟨j.val, hj⟩
  have hiCast : i.castSucc = j := Fin.ext rfl
  have hiSucc : i.succ = k := Fin.ext hjk
  let D := P.connector r i
  refine ⟨D.penultimate, ?_, P.first r k, ?_, ?_⟩
  · apply Finset.mem_union.mpr
    right
    change D.penultimate ∈ (P.attachment r j).vertexSet
    rw [attachment, dif_pos hj]
    exact D.dropLast.target_mem_vertexSet
  · exact Finset.mem_union.mpr (Or.inl (C.hull_subset k r (P.first_mem_rowHull r k)))
  · have hadj := D.penultimate_adj_target (P.connector_nontrivial r i)
    change G.Adj D.penultimate (P.first r i.succ) at hadj
    rw [hiSucc] at hadj
    exact hadj

/-- The disjoint connected extended parts realize every edge of the
assembled grill by an actual host edge. -/
def minorModel (C : ColumnPartitions P) : MinorModel C.grillGraph G where
  branchSet := C.extendedBranch
  branch_nonempty := fun x ↦ ⟨P.first x.1 x.2,
    Finset.mem_union.mpr (Or.inl (C.hull_subset x.2 x.1 (P.first_mem_rowHull x.1 x.2)))⟩
  branch_connected := C.extendedBranch_connected
  branch_disjoint := fun _ _ hxy ↦ C.extendedBranch_disjoint hxy
  adjacent := by
    intro x y hxy
    rcases hxy with ⟨hc, hcol⟩ | ⟨hr, hrow⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := hcol.2
      refine ⟨a, Finset.mem_union.mpr (Or.inl ha), b, ?_, hab⟩
      apply Finset.mem_union.mpr
      left
      rw [← hc]
      exact hb
    · rcases _root_.SimpleGraph.pathGraph_adj.mp hrow with hjk | hkj
      · obtain ⟨a, ha, b, hb, hab⟩ := C.extendedBranch_horizontal x.1 x.2 y.2 hjk
        exact ⟨a, ha, b, by
          change b ∈ C.extendedBranch (y.1, y.2)
          rw [← hr]
          exact hb, hab⟩
      · obtain ⟨b, hb, a, ha, hba⟩ := C.extendedBranch_horizontal x.1 y.2 x.2 hkj
        exact ⟨a, ha, b, by
          change b ∈ C.extendedBranch (y.1, y.2)
          rw [← hr]
          exact hb, hba.symm⟩

end ColumnPartitions

/-- A full ordered pregrill with at least one row and column contains
an ordinary grill minor of exactly the same dimensions. -/
theorem exists_grillMinor [Fintype V]
    (P : FullPregrill G m (n + 1)) (hm : 0 < m) :
    ∃ H : _root_.SimpleGraph (Fin m × Fin (n + 1)), Erdos73.IsGrill H ∧ IsMinor H G := by
  let C := P.chooseColumnPartitions hm
  exact ⟨C.grillGraph, C.grillGraph_isGrill, ⟨C.minorModel⟩⟩

theorem exists_grillMinor_of_pos [Fintype V]
    (P : FullPregrill G m n) (hm : 0 < m) (hn : 0 < n) :
    ∃ H : _root_.SimpleGraph (Fin m × Fin n), Erdos73.IsGrill H ∧ IsMinor H G := by
  cases n with
  | zero => omega
  | succ n => exact P.exists_grillMinor hm

end
end Erdos73Infrastructure.SimpleGraph.FullPregrill
