import ErdosProblems.Erdos577.FirstPawEightModel
import ErdosProblems.Erdos577.UpperCounts

/-! Exact adjacency transport for pattern (8), including its optional second diagonal. -/

namespace Erdos577.FirstPawEight

private lemma first_diagonal_adj (d : Fin 4) (h : d.val.testBit 0 = true) :
    (graph d).Adj 4 6 := by
  have hh : ∀ d : Fin 4, d.val.testBit 0 = true → (graph d).Adj 4 6 := by decide +kernel
  exact hh d h

private lemma second_diagonal_adj (d : Fin 4) (h : d.val.testBit 1 = true) :
    (graph d).Adj 5 7 := by
  have hh : ∀ d : Fin 4, d.val.testBit 1 = true → (graph d).Adj 5 7 := by decide +kernel
  exact hh d h

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma adj_upper (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (i j : Fin 8) (hadj : G.Adj (PawEncoding.labeling p q hd i)
      (PawEncoding.labeling p q hd j)) : (graph (Unattached.diagonal q)).Adj i j := by
  fin_cases i <;> fin_cases j
  · change G.Adj (p.vertices 0) (p.vertices 0) at hadj
    exact False.elim (G.irrefl hadj)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (p.vertices 0) (p.vertices 2) at hadj
    exact False.elim (hleaf.1 hadj)
  · change G.Adj (p.vertices 0) (p.vertices 3) at hadj
    exact False.elim (hleaf.2 hadj)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (p.vertices 0) (q 1) at hadj
    have hn : ¬(1 : ℕ).testBit 1 = true := by decide
    exact False.elim (hn ((h.2 0 1).mp hadj))
  · change G.Adj (p.vertices 0) (q 2) at hadj
    have hn : ¬(1 : ℕ).testBit 2 = true := by decide
    exact False.elim (hn ((h.2 0 2).mp hadj))
  · change G.Adj (p.vertices 0) (q 3) at hadj
    have hn : ¬(1 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 0 3).mp hadj))
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (p.vertices 1) (p.vertices 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (p.vertices 2) (p.vertices 0) at hadj
    exact False.elim (hleaf.1 hadj.symm)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (p.vertices 2) (p.vertices 2) at hadj
    exact False.elim (G.irrefl hadj)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (p.vertices 3) (p.vertices 0) at hadj
    exact False.elim (hleaf.2 hadj.symm)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (p.vertices 3) (p.vertices 3) at hadj
    exact False.elim (G.irrefl hadj)
  · change G.Adj (p.vertices 3) (q 0) at hadj
    have hn : ¬(0 : ℕ).testBit 0 = true := by decide
    exact False.elim (hn ((h.2 3 0).mp hadj))
  · change G.Adj (p.vertices 3) (q 1) at hadj
    have hn : ¬(0 : ℕ).testBit 1 = true := by decide
    exact False.elim (hn ((h.2 3 1).mp hadj))
  · change G.Adj (p.vertices 3) (q 2) at hadj
    have hn : ¬(0 : ℕ).testBit 2 = true := by decide
    exact False.elim (hn ((h.2 3 2).mp hadj))
  · change G.Adj (p.vertices 3) (q 3) at hadj
    have hn : ¬(0 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 3 3).mp hadj))
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 0) (p.vertices 3) at hadj
    have hn : ¬(0 : ℕ).testBit 0 = true := by decide
    exact False.elim (hn ((h.2 3 0).mp hadj.symm))
  · change G.Adj (q 0) (q 0) at hadj
    exact False.elim (G.irrefl hadj)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 0) (q 2) at hadj
    exact (first_diagonal_adj (Unattached.diagonal q)
      ((Unattached.diagonal_first q).mpr hadj))
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 1) (p.vertices 0) at hadj
    have hn : ¬(1 : ℕ).testBit 1 = true := by decide
    exact False.elim (hn ((h.2 0 1).mp hadj.symm))
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 1) (p.vertices 3) at hadj
    have hn : ¬(0 : ℕ).testBit 1 = true := by decide
    exact False.elim (hn ((h.2 3 1).mp hadj.symm))
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 1) (q 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 1) (q 3) at hadj
    exact (second_diagonal_adj (Unattached.diagonal q)
      ((Unattached.diagonal_second q).mpr hadj))
  · change G.Adj (q 2) (p.vertices 0) at hadj
    have hn : ¬(1 : ℕ).testBit 2 = true := by decide
    exact False.elim (hn ((h.2 0 2).mp hadj.symm))
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 2) (p.vertices 3) at hadj
    have hn : ¬(0 : ℕ).testBit 2 = true := by decide
    exact False.elim (hn ((h.2 3 2).mp hadj.symm))
  · change G.Adj (q 2) (q 0) at hadj
    exact (first_diagonal_adj (Unattached.diagonal q)
      ((Unattached.diagonal_first q).mpr hadj.symm)).symm
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 2) (q 2) at hadj
    exact False.elim (G.irrefl hadj)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 3) (p.vertices 0) at hadj
    have hn : ¬(1 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 0 3).mp hadj.symm))
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 3) (p.vertices 3) at hadj
    have hn : ¬(0 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 3 3).mp hadj.symm))
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 3) (q 1) at hadj
    exact (second_diagonal_adj (Unattached.diagonal q)
      ((Unattached.diagonal_second q).mpr hadj.symm)).symm
  · exact (PawModel.graph_zero_le (Unattached.diagonal q) 4081) (by decide +kernel)
  · change G.Adj (q 3) (q 3) at hadj
    exact False.elim (G.irrefl hadj)

lemma adj_iff (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (i j : Fin 8) :
    G.Adj (PawEncoding.labeling p q hd i) (PawEncoding.labeling p q hd j) ↔
      (graph (Unattached.diagonal q)).Adj i j :=
  ⟨adj_upper p q hd h hleaf i j, fun hh ↦ (coreCopy p q hd h).toHom.map_rel' hh⟩

end Erdos577.FirstPawEight
