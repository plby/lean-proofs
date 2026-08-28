import ErdosProblems.Erdos577.FirstPawSixCaseModel

/-! Exact adjacency transport for each of the five remaining pattern (6) models. -/

namespace Erdos577.FirstPawSix.CaseModel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma adj_upper (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : PawBlock.OnlyFirst q) (tag : Fin 5)
    (hrows : PawBlock.ExactRows p q (caseRows tag))
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (i j : Fin 8) (hadj : G.Adj (PawEncoding.labeling p q hd i)
      (PawEncoding.labeling p q hd j)) : (graph tag).Adj i j := by
  fin_cases i <;> fin_cases j
  · change G.Adj (p.vertices 0) (p.vertices 0) at hadj
    exact False.elim (G.irrefl hadj)
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 0 1 := by decide +kernel
    exact hh tag
  · change G.Adj (p.vertices 0) (p.vertices 2) at hadj
    exact False.elim (hleaf.1 hadj)
  · change G.Adj (p.vertices 0) (p.vertices 3) at hadj
    exact False.elim (hleaf.2 hadj)
  · change G.Adj (p.vertices 0) (q 0) at hadj
    exact ((cross_adj tag 0 0).mpr ((hrows 0 0).mp hadj))
  · change G.Adj (p.vertices 0) (q 1) at hadj
    exact ((cross_adj tag 0 1).mpr ((hrows 0 1).mp hadj))
  · change G.Adj (p.vertices 0) (q 2) at hadj
    exact ((cross_adj tag 0 2).mpr ((hrows 0 2).mp hadj))
  · change G.Adj (p.vertices 0) (q 3) at hadj
    exact ((cross_adj tag 0 3).mpr ((hrows 0 3).mp hadj))
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 1 0 := by decide +kernel
    exact hh tag
  · change G.Adj (p.vertices 1) (p.vertices 1) at hadj
    exact False.elim (G.irrefl hadj)
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 1 2 := by decide +kernel
    exact hh tag
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 1 3 := by decide +kernel
    exact hh tag
  · change G.Adj (p.vertices 1) (q 0) at hadj
    exact ((cross_adj tag 1 0).mpr ((hrows 1 0).mp hadj))
  · change G.Adj (p.vertices 1) (q 1) at hadj
    exact ((cross_adj tag 1 1).mpr ((hrows 1 1).mp hadj))
  · change G.Adj (p.vertices 1) (q 2) at hadj
    exact ((cross_adj tag 1 2).mpr ((hrows 1 2).mp hadj))
  · change G.Adj (p.vertices 1) (q 3) at hadj
    exact ((cross_adj tag 1 3).mpr ((hrows 1 3).mp hadj))
  · change G.Adj (p.vertices 2) (p.vertices 0) at hadj
    exact False.elim (hleaf.1 hadj.symm)
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 2 1 := by decide +kernel
    exact hh tag
  · change G.Adj (p.vertices 2) (p.vertices 2) at hadj
    exact False.elim (G.irrefl hadj)
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 2 3 := by decide +kernel
    exact hh tag
  · change G.Adj (p.vertices 2) (q 0) at hadj
    exact ((cross_adj tag 2 0).mpr ((hrows 2 0).mp hadj))
  · change G.Adj (p.vertices 2) (q 1) at hadj
    exact ((cross_adj tag 2 1).mpr ((hrows 2 1).mp hadj))
  · change G.Adj (p.vertices 2) (q 2) at hadj
    exact ((cross_adj tag 2 2).mpr ((hrows 2 2).mp hadj))
  · change G.Adj (p.vertices 2) (q 3) at hadj
    exact ((cross_adj tag 2 3).mpr ((hrows 2 3).mp hadj))
  · change G.Adj (p.vertices 3) (p.vertices 0) at hadj
    exact False.elim (hleaf.2 hadj.symm)
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 3 1 := by decide +kernel
    exact hh tag
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 3 2 := by decide +kernel
    exact hh tag
  · change G.Adj (p.vertices 3) (p.vertices 3) at hadj
    exact False.elim (G.irrefl hadj)
  · change G.Adj (p.vertices 3) (q 0) at hadj
    exact ((cross_adj tag 3 0).mpr ((hrows 3 0).mp hadj))
  · change G.Adj (p.vertices 3) (q 1) at hadj
    exact ((cross_adj tag 3 1).mpr ((hrows 3 1).mp hadj))
  · change G.Adj (p.vertices 3) (q 2) at hadj
    exact ((cross_adj tag 3 2).mpr ((hrows 3 2).mp hadj))
  · change G.Adj (p.vertices 3) (q 3) at hadj
    exact ((cross_adj tag 3 3).mpr ((hrows 3 3).mp hadj))
  · change G.Adj (q 0) (p.vertices 0) at hadj
    exact ((cross_adj tag 0 0).mpr ((hrows 0 0).mp hadj.symm)).symm
  · change G.Adj (q 0) (p.vertices 1) at hadj
    exact ((cross_adj tag 1 0).mpr ((hrows 1 0).mp hadj.symm)).symm
  · change G.Adj (q 0) (p.vertices 2) at hadj
    exact ((cross_adj tag 2 0).mpr ((hrows 2 0).mp hadj.symm)).symm
  · change G.Adj (q 0) (p.vertices 3) at hadj
    exact ((cross_adj tag 3 0).mpr ((hrows 3 0).mp hadj.symm)).symm
  · change G.Adj (q 0) (q 0) at hadj
    exact False.elim (G.irrefl hadj)
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 4 5 := by decide +kernel
    exact hh tag
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 4 6 := by decide +kernel
    exact hh tag
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 4 7 := by decide +kernel
    exact hh tag
  · change G.Adj (q 1) (p.vertices 0) at hadj
    exact ((cross_adj tag 0 1).mpr ((hrows 0 1).mp hadj.symm)).symm
  · change G.Adj (q 1) (p.vertices 1) at hadj
    exact ((cross_adj tag 1 1).mpr ((hrows 1 1).mp hadj.symm)).symm
  · change G.Adj (q 1) (p.vertices 2) at hadj
    exact ((cross_adj tag 2 1).mpr ((hrows 2 1).mp hadj.symm)).symm
  · change G.Adj (q 1) (p.vertices 3) at hadj
    exact ((cross_adj tag 3 1).mpr ((hrows 3 1).mp hadj.symm)).symm
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 5 4 := by decide +kernel
    exact hh tag
  · change G.Adj (q 1) (q 1) at hadj
    exact False.elim (G.irrefl hadj)
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 5 6 := by decide +kernel
    exact hh tag
  · change G.Adj (q 1) (q 3) at hadj
    exact False.elim (hdiag.2 hadj)
  · change G.Adj (q 2) (p.vertices 0) at hadj
    exact ((cross_adj tag 0 2).mpr ((hrows 0 2).mp hadj.symm)).symm
  · change G.Adj (q 2) (p.vertices 1) at hadj
    exact ((cross_adj tag 1 2).mpr ((hrows 1 2).mp hadj.symm)).symm
  · change G.Adj (q 2) (p.vertices 2) at hadj
    exact ((cross_adj tag 2 2).mpr ((hrows 2 2).mp hadj.symm)).symm
  · change G.Adj (q 2) (p.vertices 3) at hadj
    exact ((cross_adj tag 3 2).mpr ((hrows 3 2).mp hadj.symm)).symm
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 6 4 := by decide +kernel
    exact hh tag
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 6 5 := by decide +kernel
    exact hh tag
  · change G.Adj (q 2) (q 2) at hadj
    exact False.elim (G.irrefl hadj)
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 6 7 := by decide +kernel
    exact hh tag
  · change G.Adj (q 3) (p.vertices 0) at hadj
    exact ((cross_adj tag 0 3).mpr ((hrows 0 3).mp hadj.symm)).symm
  · change G.Adj (q 3) (p.vertices 1) at hadj
    exact ((cross_adj tag 1 3).mpr ((hrows 1 3).mp hadj.symm)).symm
  · change G.Adj (q 3) (p.vertices 2) at hadj
    exact ((cross_adj tag 2 3).mpr ((hrows 2 3).mp hadj.symm)).symm
  · change G.Adj (q 3) (p.vertices 3) at hadj
    exact ((cross_adj tag 3 3).mpr ((hrows 3 3).mp hadj.symm)).symm
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 7 4 := by decide +kernel
    exact hh tag
  · change G.Adj (q 3) (q 1) at hadj
    exact False.elim (hdiag.2 hadj.symm)
  · have hh : ∀ tag : Fin 5, (graph tag).Adj 7 6 := by decide +kernel
    exact hh tag
  · change G.Adj (q 3) (q 3) at hadj
    exact False.elim (G.irrefl hadj)

lemma adj_iff (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : PawBlock.OnlyFirst q) (tag : Fin 5)
    (hrows : PawBlock.ExactRows p q (caseRows tag))
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (i j : Fin 8) : G.Adj (PawEncoding.labeling p q hd i)
      (PawEncoding.labeling p q hd j) ↔ (graph tag).Adj i j := by
  classical
  exact ⟨adj_upper p q hd hdiag tag hrows hleaf i j,
    fun he ↦ (copy p q hd hdiag.1 tag hrows).toHom.map_rel' he⟩

end Erdos577.FirstPawSix.CaseModel
