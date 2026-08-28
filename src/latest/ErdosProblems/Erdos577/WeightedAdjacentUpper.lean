import ErdosProblems.Erdos577.WeightedAdjacentModel

/-! Negative row information gives an upper graph and the exact inside bound fifteen. -/

namespace Erdos577.WeightedAdjacent

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma Rows.adj_upper (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ¬G.Adj p.center (q 0) ∧ ¬G.Adj p.center (q 1))
    (i j : Fin 8)
    (hadj : G.Adj (PawEncoding.labeling p q hd i) (PawEncoding.labeling p q hd j)) :
    (graph twenty).Adj i j := by
  cases twenty
  · fin_cases i <;> fin_cases j
    · change G.Adj (p.vertices 0) (p.vertices 0) at hadj
      exact False.elim (G.irrefl hadj)
    · exact by decide +kernel
    · change G.Adj (p.vertices 0) (p.vertices 2) at hadj
      exact False.elim (hleaf.1 hadj)
    · change G.Adj (p.vertices 0) (p.vertices 3) at hadj
      exact False.elim (hleaf.2 hadj)
    · exact by decide +kernel
    · exact by decide +kernel
    · change G.Adj (p.vertices 0) (q 2) at hadj
      have hb := (h.2.1 2).mp hadj
      exact False.elim ((by decide : ((3 : ℕ).testBit 2 = true) → False) hb)
    · change G.Adj (p.vertices 0) (q 3) at hadj
      have hb := (h.2.1 3).mp hadj
      exact False.elim ((by decide : ((3 : ℕ).testBit 3 = true) → False) hb)
    · exact by decide +kernel
    · change G.Adj (p.vertices 1) (p.vertices 1) at hadj
      exact False.elim (G.irrefl hadj)
    · exact by decide +kernel
    · exact by decide +kernel
    · change G.Adj (p.vertices 1) (q 0) at hadj
      exact False.elim (hcenter.1 hadj)
    · change G.Adj (p.vertices 1) (q 1) at hadj
      exact False.elim (hcenter.2 hadj)
    · exact by decide +kernel
    · exact by decide +kernel
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
      exact False.elim ((by decide : ((4 : ℕ).testBit 0 = true) → False) hb)
    · change G.Adj (p.vertices 3) (q 1) at hadj
      have hb := (h.2.2.2 1).mp hadj
      exact False.elim ((by decide : ((4 : ℕ).testBit 1 = true) → False) hb)
    · exact by decide +kernel
    · change G.Adj (p.vertices 3) (q 3) at hadj
      have hb := (h.2.2.2 3).mp hadj
      exact False.elim ((by decide : ((4 : ℕ).testBit 3 = true) → False) hb)
    · exact by decide +kernel
    · change G.Adj (q 0) (p.vertices 1) at hadj
      exact False.elim (hcenter.1 hadj.symm)
    · exact by decide +kernel
    · change G.Adj (q 0) (p.vertices 3) at hadj
      have hb := (h.2.2.2 0).mp hadj.symm
      exact False.elim ((by decide : ((4 : ℕ).testBit 0 = true) → False) hb)
    · change G.Adj (q 0) (q 0) at hadj
      exact False.elim (G.irrefl hadj)
    · exact by decide +kernel
    · exact by decide +kernel
    · exact by decide +kernel
    · exact by decide +kernel
    · change G.Adj (q 1) (p.vertices 1) at hadj
      exact False.elim (hcenter.2 hadj.symm)
    · exact by decide +kernel
    · change G.Adj (q 1) (p.vertices 3) at hadj
      have hb := (h.2.2.2 1).mp hadj.symm
      exact False.elim ((by decide : ((4 : ℕ).testBit 1 = true) → False) hb)
    · exact by decide +kernel
    · change G.Adj (q 1) (q 1) at hadj
      exact False.elim (G.irrefl hadj)
    · exact by decide +kernel
    · change G.Adj (q 1) (q 3) at hadj
      exact False.elim (h.1.2 hadj)
    · change G.Adj (q 2) (p.vertices 0) at hadj
      have hb := (h.2.1 2).mp hadj.symm
      exact False.elim ((by decide : ((3 : ℕ).testBit 2 = true) → False) hb)
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
      exact False.elim ((by decide : ((3 : ℕ).testBit 3 = true) → False) hb)
    · exact by decide +kernel
    · exact by decide +kernel
    · change G.Adj (q 3) (p.vertices 3) at hadj
      have hb := (h.2.2.2 3).mp hadj.symm
      exact False.elim ((by decide : ((4 : ℕ).testBit 3 = true) → False) hb)
    · exact by decide +kernel
    · change G.Adj (q 3) (q 1) at hadj
      exact False.elim (h.1.2 hadj.symm)
    · exact by decide +kernel
    · change G.Adj (q 3) (q 3) at hadj
      exact False.elim (G.irrefl hadj)
  · fin_cases i <;> fin_cases j
    · change G.Adj (p.vertices 0) (p.vertices 0) at hadj
      exact False.elim (G.irrefl hadj)
    · exact by decide +kernel
    · change G.Adj (p.vertices 0) (p.vertices 2) at hadj
      exact False.elim (hleaf.1 hadj)
    · change G.Adj (p.vertices 0) (p.vertices 3) at hadj
      exact False.elim (hleaf.2 hadj)
    · exact by decide +kernel
    · exact by decide +kernel
    · change G.Adj (p.vertices 0) (q 2) at hadj
      have hb := (h.2.1 2).mp hadj
      exact False.elim ((by decide : ((3 : ℕ).testBit 2 = true) → False) hb)
    · change G.Adj (p.vertices 0) (q 3) at hadj
      have hb := (h.2.1 3).mp hadj
      exact False.elim ((by decide : ((3 : ℕ).testBit 3 = true) → False) hb)
    · exact by decide +kernel
    · change G.Adj (p.vertices 1) (p.vertices 1) at hadj
      exact False.elim (G.irrefl hadj)
    · exact by decide +kernel
    · exact by decide +kernel
    · change G.Adj (p.vertices 1) (q 0) at hadj
      exact False.elim (hcenter.1 hadj)
    · change G.Adj (p.vertices 1) (q 1) at hadj
      exact False.elim (hcenter.2 hadj)
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
      have hb := (h.2.2.1 1).mp hadj
      exact False.elim ((by decide : ((13 : ℕ).testBit 1 = true) → False) hb)
    · exact by decide +kernel
    · exact by decide +kernel
    · change G.Adj (p.vertices 3) (p.vertices 0) at hadj
      exact False.elim (hleaf.2 hadj.symm)
    · exact by decide +kernel
    · exact by decide +kernel
    · change G.Adj (p.vertices 3) (p.vertices 3) at hadj
      exact False.elim (G.irrefl hadj)
    · exact by decide +kernel
    · change G.Adj (p.vertices 3) (q 1) at hadj
      have hb := (h.2.2.2 1).mp hadj
      exact False.elim ((by decide : ((5 : ℕ).testBit 1 = true) → False) hb)
    · exact by decide +kernel
    · change G.Adj (p.vertices 3) (q 3) at hadj
      have hb := (h.2.2.2 3).mp hadj
      exact False.elim ((by decide : ((5 : ℕ).testBit 3 = true) → False) hb)
    · exact by decide +kernel
    · change G.Adj (q 0) (p.vertices 1) at hadj
      exact False.elim (hcenter.1 hadj.symm)
    · exact by decide +kernel
    · exact by decide +kernel
    · change G.Adj (q 0) (q 0) at hadj
      exact False.elim (G.irrefl hadj)
    · exact by decide +kernel
    · exact by decide +kernel
    · exact by decide +kernel
    · exact by decide +kernel
    · change G.Adj (q 1) (p.vertices 1) at hadj
      exact False.elim (hcenter.2 hadj.symm)
    · change G.Adj (q 1) (p.vertices 2) at hadj
      have hb := (h.2.2.1 1).mp hadj.symm
      exact False.elim ((by decide : ((13 : ℕ).testBit 1 = true) → False) hb)
    · change G.Adj (q 1) (p.vertices 3) at hadj
      have hb := (h.2.2.2 1).mp hadj.symm
      exact False.elim ((by decide : ((5 : ℕ).testBit 1 = true) → False) hb)
    · exact by decide +kernel
    · change G.Adj (q 1) (q 1) at hadj
      exact False.elim (G.irrefl hadj)
    · exact by decide +kernel
    · change G.Adj (q 1) (q 3) at hadj
      exact False.elim (h.1.2 hadj)
    · change G.Adj (q 2) (p.vertices 0) at hadj
      have hb := (h.2.1 2).mp hadj.symm
      exact False.elim ((by decide : ((3 : ℕ).testBit 2 = true) → False) hb)
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
      exact False.elim ((by decide : ((3 : ℕ).testBit 3 = true) → False) hb)
    · exact by decide +kernel
    · exact by decide +kernel
    · change G.Adj (q 3) (p.vertices 3) at hadj
      have hb := (h.2.2.2 3).mp hadj.symm
      exact False.elim ((by decide : ((5 : ℕ).testBit 3 = true) → False) hb)
    · exact by decide +kernel
    · change G.Adj (q 3) (q 1) at hadj
      exact False.elim (h.1.2 hadj.symm)
    · exact by decide +kernel
    · change G.Adj (q 3) (q 3) at hadj
      exact False.elim (G.irrefl hadj)

variable [DecidableRel G.Adj]

lemma Rows.inside_bound (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ¬G.Adj p.center (q 0) ∧ ¬G.Adj p.center (q 1)) :
    contacts G {q 1, p.vertices 0, p.vertices 1, p.vertices 3} (p.support ∪ q.support) ≤ 15 := by
  let e := PawEncoding.labeling p q hd
  have hinj : Function.Injective (e : Fin 8 → V) := e.injective
  have hp : pathSet.image e = {q 1, p.vertices 0, p.vertices 1, p.vertices 3} := by
    simp only [pathSet, image_insert, image_singleton]
    rfl
  have he : univ.image e = p.support ∪ q.support := PawEncoding.labeling_image p q hd
  have hb := contacts_image_le_of_adj G (graph twenty) e hinj pathSet univ
    (fun i _ j _ hij ↦ h.adj_upper twenty p q hd hleaf hcenter i j hij)
  rw [hp, he] at hb
  exact hb.trans (inside_count twenty)

end Erdos577.WeightedAdjacent
