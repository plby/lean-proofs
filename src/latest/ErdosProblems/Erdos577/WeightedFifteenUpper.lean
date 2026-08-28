import ErdosProblems.Erdos577.WeightedFifteenModel
import ErdosProblems.Erdos577.UpperCounts

/-! The optional center contact is retained in the actual inside-count upper graph. -/

namespace Erdos577.WeightedFifteen

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma adj_upper (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern15 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ∀ j : Fin 4, j ≠ 2 → ¬G.Adj p.center (q j))
    (i j : Fin 8) (hadj : G.Adj (PawEncoding.labeling p q hd i) (PawEncoding.labeling p q hd j)) :
    upperGraph.Adj i j := by
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
    have hb := (h.2.1 1).mp hadj
    exact False.elim ((by decide : ((1 : ℕ).testBit 1 = true) → False) hb)
  · change G.Adj (p.vertices 0) (q 2) at hadj
    have hb := (h.2.1 2).mp hadj
    exact False.elim ((by decide : ((1 : ℕ).testBit 2 = true) → False) hb)
  · change G.Adj (p.vertices 0) (q 3) at hadj
    have hb := (h.2.1 3).mp hadj
    exact False.elim ((by decide : ((1 : ℕ).testBit 3 = true) → False) hb)
  · exact by decide +kernel
  · change G.Adj (p.vertices 1) (p.vertices 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 1) (q 0) at hadj
    exact False.elim (hcenter 0 (by decide) hadj)
  · change G.Adj (p.vertices 1) (q 1) at hadj
    exact False.elim (hcenter 1 (by decide) hadj)
  · exact by decide +kernel
  · change G.Adj (p.vertices 1) (q 3) at hadj
    exact False.elim (hcenter 3 (by decide) hadj)
  · change G.Adj (p.vertices 2) (p.vertices 0) at hadj
    exact False.elim (hleaf.1 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (p.vertices 2) (p.vertices 2) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 3) (p.vertices 0) at hadj
    exact False.elim (hleaf.2 hadj.symm)
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 3) (p.vertices 3) at hadj
    exact False.elim (G.irrefl hadj)
  · change G.Adj (p.vertices 3) (q 0) at hadj
    have hb := (h.2.2.2 0).mp hadj
    exact False.elim ((by decide : ((6 : ℕ).testBit 0 = true) → False) hb)
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 3) (q 3) at hadj
    have hb := (h.2.2.2 3).mp hadj
    exact False.elim ((by decide : ((6 : ℕ).testBit 3 = true) → False) hb)
  · exact by decide +kernel
  · change G.Adj (q 0) (p.vertices 1) at hadj
    exact False.elim (hcenter 0 (by decide) hadj.symm)
  · exact by decide +kernel
  · change G.Adj (q 0) (p.vertices 3) at hadj
    have hb := (h.2.2.2 0).mp hadj.symm
    exact False.elim ((by decide : ((6 : ℕ).testBit 0 = true) → False) hb)
  · change G.Adj (q 0) (q 0) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 1) (p.vertices 0) at hadj
    have hb := (h.2.1 1).mp hadj.symm
    exact False.elim ((by decide : ((1 : ℕ).testBit 1 = true) → False) hb)
  · change G.Adj (q 1) (p.vertices 1) at hadj
    exact False.elim (hcenter 1 (by decide) hadj.symm)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 1) (q 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · change G.Adj (q 1) (q 3) at hadj
    exact False.elim (h.1.2 hadj)
  · change G.Adj (q 2) (p.vertices 0) at hadj
    have hb := (h.2.1 2).mp hadj.symm
    exact False.elim ((by decide : ((1 : ℕ).testBit 2 = true) → False) hb)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 2) (q 2) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · change G.Adj (q 3) (p.vertices 0) at hadj
    have hb := (h.2.1 3).mp hadj.symm
    exact False.elim ((by decide : ((1 : ℕ).testBit 3 = true) → False) hb)
  · change G.Adj (q 3) (p.vertices 1) at hadj
    exact False.elim (hcenter 3 (by decide) hadj.symm)
  · exact by decide +kernel
  · change G.Adj (q 3) (p.vertices 3) at hadj
    have hb := (h.2.2.2 3).mp hadj.symm
    exact False.elim ((by decide : ((6 : ℕ).testBit 3 = true) → False) hb)
  · exact by decide +kernel
  · change G.Adj (q 3) (q 1) at hadj
    exact False.elim (h.1.2 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (q 3) (q 3) at hadj
    exact False.elim (G.irrefl hadj)

end Erdos577.WeightedFifteen
