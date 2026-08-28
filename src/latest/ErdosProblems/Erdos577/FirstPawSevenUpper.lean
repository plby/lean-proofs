import ErdosProblems.Erdos577.FirstPawSevenModel
import ErdosProblems.Erdos577.UpperCounts

/-! Every actual core adjacency lies in the eighteen-edge pattern (7) model. -/

namespace Erdos577.FirstPawSeven

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma adj_upper (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern7 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (i j : Fin 8) (hadj : G.Adj (PawEncoding.labeling p q hd i)
      (PawEncoding.labeling p q hd j)) : graph.Adj i j := by
  fin_cases i <;> fin_cases j
  · change G.Adj (p.vertices 0) (p.vertices 0) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · change G.Adj (p.vertices 0) (p.vertices 2) at hadj
    exact False.elim (hleaf.1 hadj)
  · change G.Adj (p.vertices 0) (p.vertices 3) at hadj
    exact False.elim (hleaf.2 hadj)
  · exact by decide +kernel
  · change G.Adj (p.vertices 0) (q 1) at hadj
    have hn : ¬(1 : ℕ).testBit 1 = true := by decide
    exact False.elim (hn ((h.2 0 1).mp hadj))
  · change G.Adj (p.vertices 0) (q 2) at hadj
    have hn : ¬(1 : ℕ).testBit 2 = true := by decide
    exact False.elim (hn ((h.2 0 2).mp hadj))
  · change G.Adj (p.vertices 0) (q 3) at hadj
    have hn : ¬(1 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 0 3).mp hadj))
  · exact by decide +kernel
  · change G.Adj (p.vertices 1) (p.vertices 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 1) (q 3) at hadj
    have hn : ¬(7 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 1 3).mp hadj))
  · change G.Adj (p.vertices 2) (p.vertices 0) at hadj
    exact False.elim (hleaf.1 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (p.vertices 2) (p.vertices 2) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 2) (q 3) at hadj
    have hn : ¬(7 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 2 3).mp hadj))
  · change G.Adj (p.vertices 3) (p.vertices 0) at hadj
    exact False.elim (hleaf.2 hadj.symm)
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 3) (p.vertices 3) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · change G.Adj (p.vertices 3) (q 1) at hadj
    have hn : ¬(5 : ℕ).testBit 1 = true := by decide
    exact False.elim (hn ((h.2 3 1).mp hadj))
  · exact by decide +kernel
  · change G.Adj (p.vertices 3) (q 3) at hadj
    have hn : ¬(5 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 3 3).mp hadj))
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 0) (q 0) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 1) (p.vertices 0) at hadj
    have hn : ¬(1 : ℕ).testBit 1 = true := by decide
    exact False.elim (hn ((h.2 0 1).mp hadj.symm))
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 1) (p.vertices 3) at hadj
    have hn : ¬(5 : ℕ).testBit 1 = true := by decide
    exact False.elim (hn ((h.2 3 1).mp hadj.symm))
  · exact by decide +kernel
  · change G.Adj (q 1) (q 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · change G.Adj (q 1) (q 3) at hadj
    exact False.elim (h.1.2 hadj)
  · change G.Adj (q 2) (p.vertices 0) at hadj
    have hn : ¬(1 : ℕ).testBit 2 = true := by decide
    exact False.elim (hn ((h.2 0 2).mp hadj.symm))
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 2) (q 2) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · change G.Adj (q 3) (p.vertices 0) at hadj
    have hn : ¬(1 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 0 3).mp hadj.symm))
  · change G.Adj (q 3) (p.vertices 1) at hadj
    have hn : ¬(7 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 1 3).mp hadj.symm))
  · change G.Adj (q 3) (p.vertices 2) at hadj
    have hn : ¬(7 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 2 3).mp hadj.symm))
  · change G.Adj (q 3) (p.vertices 3) at hadj
    have hn : ¬(5 : ℕ).testBit 3 = true := by decide
    exact False.elim (hn ((h.2 3 3).mp hadj.symm))
  · exact by decide +kernel
  · change G.Adj (q 3) (q 1) at hadj
    exact False.elim (h.1.2 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (q 3) (q 3) at hadj
    exact False.elim (G.irrefl hadj)

end Erdos577.FirstPawSeven
