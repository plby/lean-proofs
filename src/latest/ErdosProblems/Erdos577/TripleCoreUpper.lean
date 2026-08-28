import ErdosProblems.Erdos577.TripleCoreCopies

/-! The copied seven-vertex core has exact adjacency, so its degree budget is preserved. -/

namespace Erdos577.TripleCorePatterns

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma SourcePattern.core_adj_upper {tag : Fin 12} {p : Paw G} {q : Quadrilateral G}
    (h : SourcePattern tag p q) (hd : Disjoint p.support q.support)
    (i : Fin 8) (hi : i ∈ core) (j : Fin 8) (hj : j ∈ core)
    (hadj : G.Adj (PawEncoding.labeling p q hd i) (PawEncoding.labeling p q hd j)) :
    (graph tag).Adj i j := by
  classical
  fin_cases i <;> fin_cases j
  · simp [core] at hi
  · simp [core] at hi
  · simp [core] at hi
  · simp [core] at hi
  · simp [core] at hi
  · simp [core] at hi
  · simp [core] at hi
  · simp [core] at hi
  · simp [core] at hj
  · exact False.elim (G.irrefl hadj)
  · have hall : ∀ tag : Fin 12, (graph tag).Adj 1 2 := by decide +kernel
    exact hall tag
  · have hall : ∀ tag : Fin 12, (graph tag).Adj 1 3 := by decide +kernel
    exact hall tag
  · change G.Adj (p.vertices 1) (q 0) at hadj
    exact (cross_adj tag 1 0).mpr ((h.2.2 1 0 (by decide)).mp hadj)
  · change G.Adj (p.vertices 1) (q 1) at hadj
    exact (cross_adj tag 1 1).mpr ((h.2.2 1 1 (by decide)).mp hadj)
  · change G.Adj (p.vertices 1) (q 2) at hadj
    exact (cross_adj tag 1 2).mpr ((h.2.2 1 2 (by decide)).mp hadj)
  · change G.Adj (p.vertices 1) (q 3) at hadj
    exact (cross_adj tag 1 3).mpr ((h.2.2 1 3 (by decide)).mp hadj)
  · simp [core] at hj
  · have hall : ∀ tag : Fin 12, (graph tag).Adj 2 1 := by decide +kernel
    exact hall tag
  · exact False.elim (G.irrefl hadj)
  · have hall : ∀ tag : Fin 12, (graph tag).Adj 2 3 := by decide +kernel
    exact hall tag
  · change G.Adj (p.vertices 2) (q 0) at hadj
    exact (cross_adj tag 2 0).mpr ((h.2.2 2 0 (by decide)).mp hadj)
  · change G.Adj (p.vertices 2) (q 1) at hadj
    exact (cross_adj tag 2 1).mpr ((h.2.2 2 1 (by decide)).mp hadj)
  · change G.Adj (p.vertices 2) (q 2) at hadj
    exact (cross_adj tag 2 2).mpr ((h.2.2 2 2 (by decide)).mp hadj)
  · change G.Adj (p.vertices 2) (q 3) at hadj
    exact (cross_adj tag 2 3).mpr ((h.2.2 2 3 (by decide)).mp hadj)
  · simp [core] at hj
  · have hall : ∀ tag : Fin 12, (graph tag).Adj 3 1 := by decide +kernel
    exact hall tag
  · have hall : ∀ tag : Fin 12, (graph tag).Adj 3 2 := by decide +kernel
    exact hall tag
  · exact False.elim (G.irrefl hadj)
  · change G.Adj (p.vertices 3) (q 0) at hadj
    exact (cross_adj tag 3 0).mpr ((h.2.2 3 0 (by decide)).mp hadj)
  · change G.Adj (p.vertices 3) (q 1) at hadj
    exact (cross_adj tag 3 1).mpr ((h.2.2 3 1 (by decide)).mp hadj)
  · change G.Adj (p.vertices 3) (q 2) at hadj
    exact (cross_adj tag 3 2).mpr ((h.2.2 3 2 (by decide)).mp hadj)
  · change G.Adj (p.vertices 3) (q 3) at hadj
    exact (cross_adj tag 3 3).mpr ((h.2.2 3 3 (by decide)).mp hadj)
  · simp [core] at hj
  · change G.Adj (q 0) (p.vertices 1) at hadj
    exact ((cross_adj tag 1 0).mpr ((h.2.2 1 0 (by decide)).mp hadj.symm)).symm
  · change G.Adj (q 0) (p.vertices 2) at hadj
    exact ((cross_adj tag 2 0).mpr ((h.2.2 2 0 (by decide)).mp hadj.symm)).symm
  · change G.Adj (q 0) (p.vertices 3) at hadj
    exact ((cross_adj tag 3 0).mpr ((h.2.2 3 0 (by decide)).mp hadj.symm)).symm
  · exact False.elim (G.irrefl hadj)
  · change G.Adj (q 0) (q 1) at hadj
    have he := (q.model_adj_iff 0 1).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 0 1).mpr he
  · change G.Adj (q 0) (q 2) at hadj
    have he := (q.model_adj_iff 0 2).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 0 2).mpr he
  · change G.Adj (q 0) (q 3) at hadj
    have he := (q.model_adj_iff 0 3).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 0 3).mpr he
  · simp [core] at hj
  · change G.Adj (q 1) (p.vertices 1) at hadj
    exact ((cross_adj tag 1 1).mpr ((h.2.2 1 1 (by decide)).mp hadj.symm)).symm
  · change G.Adj (q 1) (p.vertices 2) at hadj
    exact ((cross_adj tag 2 1).mpr ((h.2.2 2 1 (by decide)).mp hadj.symm)).symm
  · change G.Adj (q 1) (p.vertices 3) at hadj
    exact ((cross_adj tag 3 1).mpr ((h.2.2 3 1 (by decide)).mp hadj.symm)).symm
  · change G.Adj (q 1) (q 0) at hadj
    have he := (q.model_adj_iff 1 0).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 1 0).mpr he
  · exact False.elim (G.irrefl hadj)
  · change G.Adj (q 1) (q 2) at hadj
    have he := (q.model_adj_iff 1 2).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 1 2).mpr he
  · change G.Adj (q 1) (q 3) at hadj
    have he := (q.model_adj_iff 1 3).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 1 3).mpr he
  · simp [core] at hj
  · change G.Adj (q 2) (p.vertices 1) at hadj
    exact ((cross_adj tag 1 2).mpr ((h.2.2 1 2 (by decide)).mp hadj.symm)).symm
  · change G.Adj (q 2) (p.vertices 2) at hadj
    exact ((cross_adj tag 2 2).mpr ((h.2.2 2 2 (by decide)).mp hadj.symm)).symm
  · change G.Adj (q 2) (p.vertices 3) at hadj
    exact ((cross_adj tag 3 2).mpr ((h.2.2 3 2 (by decide)).mp hadj.symm)).symm
  · change G.Adj (q 2) (q 0) at hadj
    have he := (q.model_adj_iff 2 0).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 2 0).mpr he
  · change G.Adj (q 2) (q 1) at hadj
    have he := (q.model_adj_iff 2 1).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 2 1).mpr he
  · exact False.elim (G.irrefl hadj)
  · change G.Adj (q 2) (q 3) at hadj
    have he := (q.model_adj_iff 2 3).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 2 3).mpr he
  · simp [core] at hj
  · change G.Adj (q 3) (p.vertices 1) at hadj
    exact ((cross_adj tag 1 3).mpr ((h.2.2 1 3 (by decide)).mp hadj.symm)).symm
  · change G.Adj (q 3) (p.vertices 2) at hadj
    exact ((cross_adj tag 2 3).mpr ((h.2.2 2 3 (by decide)).mp hadj.symm)).symm
  · change G.Adj (q 3) (p.vertices 3) at hadj
    exact ((cross_adj tag 3 3).mpr ((h.2.2 3 3 (by decide)).mp hadj.symm)).symm
  · change G.Adj (q 3) (q 0) at hadj
    have he := (q.model_adj_iff 3 0).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 3 0).mpr he
  · change G.Adj (q 3) (q 1) at hadj
    have he := (q.model_adj_iff 3 1).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 3 1).mpr he
  · change G.Adj (q 3) (q 2) at hadj
    have he := (q.model_adj_iff 3 2).mpr hadj
    rw [h.diagonal_eq] at he
    exact (right_adj tag 3 2).mpr he
  · exact False.elim (G.irrefl hadj)

lemma SourcePattern.core_adj_iff {tag : Fin 12} {p : Paw G} {q : Quadrilateral G}
    (h : SourcePattern tag p q) (hd : Disjoint p.support q.support)
    (i : Fin 8) (hi : i ∈ core) (j : Fin 8) (hj : j ∈ core) :
    G.Adj (h.copy hd i) (h.copy hd j) ↔ (graph tag).Adj i j :=
  ⟨h.core_adj_upper hd i hi j hj, fun he ↦ (h.copy hd).toHom.map_rel' he⟩

end Erdos577.TripleCorePatterns
