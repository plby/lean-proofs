import ErdosProblems.Erdos577.WeightedFourteenDenseModel
import ErdosProblems.Erdos577.WeightedFourteenUpper

/-! Only the four terminal rows are needed for the inside upper bound eighteen. -/

namespace Erdos577.WeightedFourteen.Dense.Model

open Finset

def upperPairs : Finset (Fin 12 × Fin 12) := {
    (0, 1), (0, 4), (0, 6), (0, 8), (0, 10),
    (5, 4), (5, 6), (5, 8), (5, 10),
    (7, 2), (7, 4), (7, 6), (7, 8), (7, 10),
    (9, 4), (9, 6), (9, 8), (9, 10)}

def upperGraph : SimpleGraph (Fin 12) :=
  SimpleGraph.fromRel fun i j ↦ (i, j) ∈ upperPairs

instance : DecidableRel upperGraph.Adj := inferInstanceAs (DecidableRel
  (SimpleGraph.fromRel (fun i j : Fin 12 ↦ (i, j) ∈ upperPairs)).Adj)

lemma terminal_inside : contacts upperGraph terminalSet univ = 18 := by decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma terminal_adj_upper (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support) (special : Fin 3)
    (hrows : Rows p q v special)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ¬G.Adj p.center (q 1) ∧ ¬G.Adj p.center (q 3))
    (tag : Fin 4) (j : Fin 12)
    (hadj : G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv (terminalIndex tag))
      (WeightedFifteen.twoBlockLabeling p q hd v hv j)) :
    upperGraph.Adj (terminalIndex tag) j := by
  fin_cases tag <;> fin_cases j
  · change G.Adj (PawEncoding.labeling p q hd 0)
      (PawEncoding.labeling p q hd 0) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 0 0 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 0 0) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 0)
      (PawEncoding.labeling p q hd 2) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 0 2 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 0 2) hh)
  · change G.Adj (PawEncoding.labeling p q hd 0)
      (PawEncoding.labeling p q hd 3) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 0 3 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 0 3) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 0)
      (PawEncoding.labeling p q hd 5) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 0 5 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 0 5) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 0)
      (PawEncoding.labeling p q hd 7) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 0 7 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 0 7) hh)
  · exact by decide +kernel
  · change G.Adj (p.vertices 0) (v 1) at hadj
    have hb := ((hrows.leaf p q v special) 1).mp hadj
    exact False.elim ((by decide : ((5 : ℕ).testBit 1 = true) → False) hb)
  · exact by decide +kernel
  · change G.Adj (p.vertices 0) (v 3) at hadj
    have hb := ((hrows.leaf p q v special) 3).mp hadj
    exact False.elim ((by decide : ((5 : ℕ).testBit 3 = true) → False) hb)
  · change G.Adj (PawEncoding.labeling p q hd 5)
      (PawEncoding.labeling p q hd 0) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 5 0 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 5 0) hh)
  · change G.Adj (PawEncoding.labeling p q hd 5)
      (PawEncoding.labeling p q hd 1) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 5 1 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 5 1) hh)
  · change G.Adj (PawEncoding.labeling p q hd 5)
      (PawEncoding.labeling p q hd 2) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 5 2 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 5 2) hh)
  · change G.Adj (PawEncoding.labeling p q hd 5)
      (PawEncoding.labeling p q hd 3) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 5 3 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 5 3) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 5)
      (PawEncoding.labeling p q hd 5) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 5 5 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 5 5) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 5)
      (PawEncoding.labeling p q hd 7) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 5 7 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 5 7) hh)
  · exact by decide +kernel
  · change G.Adj (q 1) (v 1) at hadj
    have hb := ((hrows.2.2.1) 1).mp hadj
    exact False.elim ((by decide : ((5 : ℕ).testBit 1 = true) → False) hb)
  · exact by decide +kernel
  · change G.Adj (q 1) (v 3) at hadj
    have hb := ((hrows.2.2.1) 3).mp hadj
    exact False.elim ((by decide : ((5 : ℕ).testBit 3 = true) → False) hb)
  · change G.Adj (PawEncoding.labeling p q hd 7)
      (PawEncoding.labeling p q hd 0) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 7 0 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 7 0) hh)
  · change G.Adj (PawEncoding.labeling p q hd 7)
      (PawEncoding.labeling p q hd 1) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 7 1 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 7 1) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 7)
      (PawEncoding.labeling p q hd 3) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 7 3 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 7 3) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 7)
      (PawEncoding.labeling p q hd 5) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 7 5 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 7 5) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 7)
      (PawEncoding.labeling p q hd 7) at hadj
    have hh := WeightedFourteen.adj_upper p q hd h hleaf hcenter 7 7 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFourteen.upperGraph.Adj 7 7) hh)
  · exact by decide +kernel
  · change G.Adj (q 3) (v 1) at hadj
    have hb := ((hrows.2.2.2) 1).mp hadj
    exact False.elim ((by decide : ((5 : ℕ).testBit 1 = true) → False) hb)
  · exact by decide +kernel
  · change G.Adj (q 3) (v 3) at hadj
    have hb := ((hrows.2.2.2) 3).mp hadj
    exact False.elim ((by decide : ((5 : ℕ).testBit 3 = true) → False) hb)
  · change G.Adj (v 1) (p.vertices 0) at hadj
    exact False.elim (hrows.paw_low_absent p q v special 0 hadj.symm)
  · change G.Adj (v 1) (p.vertices 1) at hadj
    exact False.elim (hrows.paw_low_absent p q v special 1 hadj.symm)
  · change G.Adj (v 1) (p.vertices 2) at hadj
    exact False.elim (hrows.paw_low_absent p q v special 2 hadj.symm)
  · change G.Adj (v 1) (p.vertices 3) at hadj
    exact False.elim (hrows.paw_low_absent p q v special 3 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (v 1) (q 1) at hadj
    have hb := (hrows.2.2.1 1).mp hadj.symm
    exact False.elim ((by decide : ((5 : ℕ).testBit 1 = true) → False) hb)
  · exact by decide +kernel
  · change G.Adj (v 1) (q 3) at hadj
    have hb := (hrows.2.2.2 1).mp hadj.symm
    exact False.elim ((by decide : ((5 : ℕ).testBit 1 = true) → False) hb)
  · exact by decide +kernel
  · change G.Adj (v 1) (v 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · change G.Adj (v 1) (v 3) at hadj
    exact False.elim (hrows.1.2 hadj)

variable [DecidableRel G.Adj]

lemma terminal_inside_bound (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (special : Fin 3) (hrows : Rows p q v special)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ¬G.Adj p.center (q 1) ∧ ¬G.Adj p.center (q 3)) :
    contacts G (terminalSet.image (WeightedFifteen.twoBlockLabeling p q hd v hv))
      ((p.support ∪ q.support) ∪ v.support) ≤ 18 := by
  let e := WeightedFifteen.twoBlockLabeling p q hd v hv
  have hl := contacts_image_le_of_adj G upperGraph e e.injective terminalSet univ (by
    intro i hi j _ hij
    rw [terminalSet_eq] at hi
    obtain ⟨tag, _, rfl⟩ := mem_image.mp hi
    exact terminal_adj_upper p q hd h v hv special hrows hleaf hcenter tag j hij)
  change contacts G (terminalSet.image e)
    (univ.image (WeightedFifteen.twoBlockLabeling p q hd v hv)) ≤ _ at hl
  rw [WeightedFifteen.twoBlockLabeling_image, terminal_inside] at hl
  exact hl

end Erdos577.WeightedFourteen.Dense.Model
