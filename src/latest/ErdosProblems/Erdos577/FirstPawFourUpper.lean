import ErdosProblems.Erdos577.FirstPawFourModel
import ErdosProblems.Erdos577.UpperCounts

/-! The full allowed pattern (4) core has repeated-leaf inside weight22. -/

namespace Erdos577.FirstPawFour

open Finset

def upperGraph : SimpleGraph (Fin 8) := SimpleGraph.fromRel fun i j ↦
  (i, j) ∈ basePairs ∪ univ.image contactPair ∪ {(5, 7)}

instance : DecidableRel upperGraph.Adj := inferInstanceAs (DecidableRel
  (SimpleGraph.fromRel (fun i j : Fin 8 ↦
    (i, j) ∈ basePairs ∪ univ.image contactPair ∪ {(5, 7)})).Adj)

def weightSet (second : Bool) : Finset (Fin 8) := if second then {0, 5, 7} else {0, 2, 3}

lemma weightSet_card (second : Bool) : (weightSet second).card = 3 := by
  cases second <;> decide +kernel

lemma inside_weight : contacts upperGraph (weightSet false) univ +
    contacts upperGraph (weightSet true) univ = 22 := by decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma adj_upper (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern4 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
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
    exact False.elim (low_absent p q h 0 1 (by decide) (Or.inl rfl) hadj)
  · exact by decide +kernel
  · change G.Adj (p.vertices 0) (q 3) at hadj
    exact False.elim (low_absent p q h 0 3 (by decide) (Or.inr rfl) hadj)
  · exact by decide +kernel
  · change G.Adj (p.vertices 1) (p.vertices 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 2) (p.vertices 0) at hadj
    exact False.elim (hleaf.1 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (p.vertices 2) (p.vertices 2) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 2) (q 1) at hadj
    exact False.elim (low_absent p q h 2 1 (by decide) (Or.inl rfl) hadj)
  · exact by decide +kernel
  · change G.Adj (p.vertices 2) (q 3) at hadj
    exact False.elim (low_absent p q h 2 3 (by decide) (Or.inr rfl) hadj)
  · change G.Adj (p.vertices 3) (p.vertices 0) at hadj
    exact False.elim (hleaf.2 hadj.symm)
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 3) (p.vertices 3) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · change G.Adj (p.vertices 3) (q 1) at hadj
    exact False.elim (low_absent p q h 3 1 (by decide) (Or.inl rfl) hadj)
  · exact by decide +kernel
  · change G.Adj (p.vertices 3) (q 3) at hadj
    exact False.elim (low_absent p q h 3 3 (by decide) (Or.inr rfl) hadj)
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
    exact False.elim (low_absent p q h 0 1 (by decide) (Or.inl rfl) hadj.symm)
  · exact by decide +kernel
  · change G.Adj (q 1) (p.vertices 2) at hadj
    exact False.elim (low_absent p q h 2 1 (by decide) (Or.inl rfl) hadj.symm)
  · change G.Adj (q 1) (p.vertices 3) at hadj
    exact False.elim (low_absent p q h 3 1 (by decide) (Or.inl rfl) hadj.symm)
  · exact by decide +kernel
  · change G.Adj (q 1) (q 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 2) (q 2) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · change G.Adj (q 3) (p.vertices 0) at hadj
    exact False.elim (low_absent p q h 0 3 (by decide) (Or.inr rfl) hadj.symm)
  · exact by decide +kernel
  · change G.Adj (q 3) (p.vertices 2) at hadj
    exact False.elim (low_absent p q h 2 3 (by decide) (Or.inr rfl) hadj.symm)
  · change G.Adj (q 3) (p.vertices 3) at hadj
    exact False.elim (low_absent p q h 3 3 (by decide) (Or.inr rfl) hadj.symm)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 3) (q 3) at hadj
    exact False.elim (G.irrefl hadj)

end Erdos577.FirstPawFour
