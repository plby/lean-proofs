/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.PregrillHulls

/-!
# Half-open connectors between consecutive expanded columns
-/

namespace Erdos73Infrastructure.SimpleGraph.FullPregrill
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} {G : _root_.SimpleGraph V} {m n : ℕ}

def connector (P : FullPregrill G m (n + 1)) (r : Fin m) (i : Fin n) : GraphPath G :=
  (P.row r).segmentOfBefore (P.last_before_first_of_lt r i.castSucc_lt_succ)

@[simp] theorem connector_source (P : FullPregrill G m (n + 1)) (r : Fin m) (i : Fin n) :
    (P.connector r i).source = P.last r i.castSucc := rfl

@[simp] theorem connector_target (P : FullPregrill G m (n + 1)) (r : Fin m) (i : Fin n) :
    (P.connector r i).target = P.first r i.succ := rfl

theorem connector_nontrivial (P : FullPregrill G m (n + 1)) (r : Fin m) (i : Fin n) :
    (P.connector r i).source ≠ (P.connector r i).target :=
  P.last_ne_first_of_ne r i.castSucc_lt_succ.ne

theorem connector_subset_row (P : FullPregrill G m (n + 1)) (r : Fin m) (i : Fin n) :
    (P.connector r i).vertexSet ⊆ (P.row r).vertexSet :=
  (P.row r).segmentOfBefore_vertexSet_subset _

theorem first_before_last_of_le (P : FullPregrill G m (n + 1)) (r : Fin m)
    {i j : Fin (n + 1)} (hij : i ≤ j) : (P.row r).Before (P.first r i) (P.last r j) := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact P.ordered i j hlt r _ (P.first_mem_column r i) (P.first_mem_row r i)
      _ (P.last_mem_column r j) (P.last_mem_row r j)
  · exact P.first_before_last r i

/-- Every retained connector vertex lying in an expanded column is the
connector's initial vertex, and the column is its own left column. -/
theorem connector_dropLast_meets_column
    (P : FullPregrill G m (n + 1)) (r : Fin m) (i : Fin n)
    {j : Fin (n + 1)} {v : V}
    (hvD : v ∈ (P.connector r i).dropLast.vertexSet) (hvK : v ∈ P.expandedColumn j) :
    j = i.castSucc ∧ v = P.last r i.castSucc := by
  have hvC := (P.connector r i).dropLast_vertexSet_subset hvD
  have hvrow := P.connector_subset_row r i hvC
  have hstart : (P.row r).Before (P.last r i.castSucc) v :=
    (P.row r).before_of_mem_segmentOfBefore_left _ hvC
  have hend : (P.row r).Before v (P.first r i.succ) :=
    (P.row r).before_of_mem_segmentOfBefore_right _ hvC
  have hvHull : v ∈ (P.rowHull r j).vertexSet := by
    rw [← P.row_inter_expandedColumn_eq_rowHull r j]
    exact Finset.mem_inter.mpr ⟨hvrow, hvK⟩
  by_cases hj : j ≤ i.castSucc
  · have hbefore : (P.row r).Before v (P.last r i.castSucc) := by
      rcases lt_or_eq_of_le hj with hlt | rfl
      · exact P.expandedColumn_ordered hlt r hvK hvrow
          (P.column_subset_expandedColumn _ (P.last_mem_column r _)) (P.last_mem_row r _)
      · exact P.before_last_of_mem_rowHull r _ hvHull
    have heq := (P.row r).before_antisymm hbefore hstart
    have hj_eq : j = i.castSucc := by
      by_contra hne
      exact Finset.disjoint_left.mp (P.expandedColumn_disjoint hne) hvK
        (heq ▸ P.column_subset_expandedColumn _ (P.last_mem_column r _))
    exact ⟨hj_eq, heq⟩
  · have hsucc : i.succ ≤ j := by
      change ¬ j.val ≤ i.val at hj
      change i.val + 1 ≤ j.val
      omega
    have hbefore : (P.row r).Before (P.first r i.succ) v := by
      rcases lt_or_eq_of_le hsucc with hlt | heq
      · exact P.expandedColumn_ordered hlt r
          (P.column_subset_expandedColumn _ (P.first_mem_column r _)) (P.first_mem_row r _)
          hvK hvrow
      · rw [heq]
        exact P.first_before_of_mem_rowHull r j hvHull
    have heq : v = (P.connector r i).target := (P.row r).before_antisymm hend hbefore
    exact ((P.connector r i).target_not_mem_dropLast_vertexSet
      (P.connector_nontrivial r i) (heq ▸ hvD)).elim

/-- Distinct half-open connectors are disjoint, including consecutive
ones that may meet at a one-vertex row hull before the endpoint is removed. -/
theorem connector_dropLast_disjoint
    (P : FullPregrill G m (n + 1)) {r s : Fin m} {i j : Fin n}
    (hne : (r, i) ≠ (s, j)) :
    Disjoint (P.connector r i).dropLast.vertexSet (P.connector s j).dropLast.vertexSet := by
  by_cases hrs : r = s
  · subst s
    have hij : i ≠ j := fun h ↦ hne (congrArg (fun k ↦ (r, k)) h)
    have hforward (a b : Fin n) (hab : a < b) :
        Disjoint (P.connector r a).dropLast.vertexSet (P.connector r b).dropLast.vertexSet := by
      have hle : a.succ ≤ b.castSucc := by
        change a.val + 1 ≤ b.val
        exact Nat.succ_le_of_lt hab
      exact (P.row r).segmentOfBefore_dropLast_disjoint_of_target_before_source
        (P.last_before_first_of_lt r a.castSucc_lt_succ)
        (P.last_before_first_of_lt r b.castSucc_lt_succ)
        (P.first_before_last_of_le r hle) (P.connector_nontrivial r a)
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hforward i j hlt
    · exact (hforward j i hgt).symm
  · exact (P.row_disjoint hrs).mono
      ((P.connector r i).dropLast_vertexSet_subset.trans (P.connector_subset_row r i))
      ((P.connector s j).dropLast_vertexSet_subset.trans (P.connector_subset_row s j))

end
end Erdos73Infrastructure.SimpleGraph.FullPregrill
