import ErdosProblems.Erdos577.WeightedFifteenDense
import ErdosProblems.Erdos577.ExactCopyCounts

/-! Positive and upper twelve-vertex graphs for the final pattern (15) exchange. -/

namespace Erdos577.WeightedFifteen.DenseModel

open Finset

def pairs : Finset (Fin 12 × Fin 12) := {
    (0, 1), (0, 4), (0, 8), (0, 9), (0, 10), (0, 11),
    (1, 2), (1, 3), (1, 8), (1, 9), (1, 10), (2, 3),
    (2, 4), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6),
    (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10),
    (5, 6), (6, 7), (8, 9), (8, 10), (8, 11), (9, 10),
    (9, 11), (10, 11)}

def extraPairs : Finset (Fin 12 × Fin 12) := {
    (1, 6), (2, 8), (2, 9), (2, 10), (2, 11), (6, 8),
    (6, 9), (6, 10), (6, 11)}

def graph : SimpleGraph (Fin 12) := SimpleGraph.fromRel fun i j ↦ (i, j) ∈ pairs

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel
  (SimpleGraph.fromRel (fun i j : Fin 12 ↦ (i, j) ∈ pairs)).Adj)

def upperGraph : SimpleGraph (Fin 12) :=
  SimpleGraph.fromRel fun i j ↦ (i, j) ∈ pairs ∪ extraPairs

instance : DecidableRel upperGraph.Adj := inferInstanceAs (DecidableRel
  (SimpleGraph.fromRel (fun i j : Fin 12 ↦ (i, j) ∈ pairs ∪ extraPairs)).Adj)

lemma graph_le_upper : graph ≤ upperGraph := by
  intro i j hij
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hij with ⟨hne, hij | hji⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl (mem_union_left _ hij)⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inr (mem_union_left _ hji)⟩

def sixSet : Finset (Fin 12) := {5, 3, 1, 0, 7, 8}

lemma sixSet_card : sixSet.card = 6 := by decide +kernel

lemma six_inside : contacts upperGraph sixSet univ = 32 := by decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def copy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern15 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v) : graph.Copy G := by
  let e := twoBlockLabeling p q hd v hv
  have hvc (i j : Fin 4) (hij : i ≠ j) : G.Adj (v i) (v j) :=
    hcl.isClique ((v.mem_support _).mpr ⟨i, rfl⟩) ((v.mem_support _).mpr ⟨j, rfl⟩)
      (fun he ↦ hij (v.injective he))
  have hpos (a : Fin 12 × Fin 12) (ha : a ∈ pairs) : G.Adj (e a.1) (e a.2) := by
    simp only [pairs, mem_insert, mem_singleton] at ha
    rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha |
      ha | ha | ha | ha | ha | ha | ha | ha | ha | ha |
      ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 0) (PawEncoding.labeling p q hd 1)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 0 1)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 0) (PawEncoding.labeling p q hd 4)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 0 4)
    · cases ha
      exact hrows.1 0
    · cases ha
      exact hrows.1 1
    · cases ha
      exact hrows.1 2
    · cases ha
      exact hrows.1 3
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 1) (PawEncoding.labeling p q hd 2)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 1 2)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 1) (PawEncoding.labeling p q hd 3)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 1 3)
    · cases ha
      exact (hrows.2.1 0).mpr (by decide)
    · cases ha
      exact (hrows.2.1 1).mpr (by decide)
    · cases ha
      exact (hrows.2.1 2).mpr (by decide)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 2) (PawEncoding.labeling p q hd 3)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 2 3)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 2) (PawEncoding.labeling p q hd 4)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 2 4)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 2) (PawEncoding.labeling p q hd 5)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 2 5)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 2) (PawEncoding.labeling p q hd 6)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 2 6)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 2) (PawEncoding.labeling p q hd 7)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 2 7)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 3) (PawEncoding.labeling p q hd 5)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 3 5)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 3) (PawEncoding.labeling p q hd 6)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 3 6)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 4) (PawEncoding.labeling p q hd 5)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 4 5)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 4) (PawEncoding.labeling p q hd 6)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 4 6)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 4) (PawEncoding.labeling p q hd 7)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 4 7)
    · cases ha
      exact (hrows.2.2.1 0).mpr (by decide)
    · cases ha
      exact (hrows.2.2.1 1).mpr (by decide)
    · cases ha
      exact (hrows.2.2.1 2).mpr (by decide)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 5) (PawEncoding.labeling p q hd 6)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 5 6)
    · cases ha
      change G.Adj (PawEncoding.labeling p q hd 6) (PawEncoding.labeling p q hd 7)
      exact (coreCopy p q hd h).toHom.map_rel'
        (by decide +kernel : WeightedFifteen.graph.Adj 6 7)
    · cases ha
      exact hvc 0 1 (by decide)
    · cases ha
      exact hvc 0 2 (by decide)
    · cases ha
      exact hvc 0 3 (by decide)
    · cases ha
      exact hvc 1 2 (by decide)
    · cases ha
      exact hvc 1 3 (by decide)
    · cases ha
      exact hvc 2 3 (by decide)
  refine ⟨⟨e, ?_⟩, e.injective⟩
  intro i j hij
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hij with ⟨_, hij | hji⟩
  · exact hpos (i, j) hij
  · exact (hpos (j, i) hji).symm

lemma copy_apply (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern15 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v) (i : Fin 12) :
    copy p q hd h v hv hcl hrows i = twoBlockLabeling p q hd v hv i := rfl

omit [DecidableRel G.Adj] in
lemma adj_upper (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern15 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support) (hrows : DenseRows p q v)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ∀ j : Fin 4, j ≠ 2 → ¬G.Adj p.center (q j))
    (i j : Fin 12) (hadj : G.Adj (twoBlockLabeling p q hd v hv i)
      (twoBlockLabeling p q hd v hv j)) : upperGraph.Adj i j := by
  fin_cases i <;> fin_cases j
  · change G.Adj (p.vertices 0) (p.vertices 0) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 0)
      (PawEncoding.labeling p q hd 2) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 0 2 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 0 2) hh)
  · change G.Adj (PawEncoding.labeling p q hd 0)
      (PawEncoding.labeling p q hd 3) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 0 3 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 0 3) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 0)
      (PawEncoding.labeling p q hd 5) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 0 5 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 0 5) hh)
  · change G.Adj (PawEncoding.labeling p q hd 0)
      (PawEncoding.labeling p q hd 6) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 0 6 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 0 6) hh)
  · change G.Adj (PawEncoding.labeling p q hd 0)
      (PawEncoding.labeling p q hd 7) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 0 7 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 0 7) hh)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 1) (p.vertices 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 1)
      (PawEncoding.labeling p q hd 4) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 1 4 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 1 4) hh)
  · change G.Adj (PawEncoding.labeling p q hd 1)
      (PawEncoding.labeling p q hd 5) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 1 5 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 1 5) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 1)
      (PawEncoding.labeling p q hd 7) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 1 7 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 1 7) hh)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 1) (v 3) at hadj
    exact False.elim (((hrows.2.1 3).mp hadj) rfl)
  · change G.Adj (PawEncoding.labeling p q hd 2)
      (PawEncoding.labeling p q hd 0) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 2 0 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 2 0) hh)
  · exact by decide +kernel
  · change G.Adj (p.vertices 2) (p.vertices 2) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 3)
      (PawEncoding.labeling p q hd 0) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 3 0 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 3 0) hh)
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (p.vertices 3) (p.vertices 3) at hadj
    exact False.elim (G.irrefl hadj)
  · change G.Adj (PawEncoding.labeling p q hd 3)
      (PawEncoding.labeling p q hd 4) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 3 4 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 3 4) hh)
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 3)
      (PawEncoding.labeling p q hd 7) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 3 7 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 3 7) hh)
  · change G.Adj (p.vertices 3) (v 0) at hadj
    exact False.elim (hrows.2.2.2.1 0 hadj)
  · change G.Adj (p.vertices 3) (v 1) at hadj
    exact False.elim (hrows.2.2.2.1 1 hadj)
  · change G.Adj (p.vertices 3) (v 2) at hadj
    exact False.elim (hrows.2.2.2.1 2 hadj)
  · change G.Adj (p.vertices 3) (v 3) at hadj
    exact False.elim (hrows.2.2.2.1 3 hadj)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 4)
      (PawEncoding.labeling p q hd 1) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 4 1 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 4 1) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 4)
      (PawEncoding.labeling p q hd 3) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 4 3 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 4 3) hh)
  · change G.Adj (q 0) (q 0) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 0) (v 3) at hadj
    exact False.elim (((hrows.2.2.1 3).mp hadj) rfl)
  · change G.Adj (PawEncoding.labeling p q hd 5)
      (PawEncoding.labeling p q hd 0) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 5 0 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 5 0) hh)
  · change G.Adj (PawEncoding.labeling p q hd 5)
      (PawEncoding.labeling p q hd 1) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 5 1 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 5 1) hh)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 1) (q 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 5)
      (PawEncoding.labeling p q hd 7) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 5 7 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 5 7) hh)
  · change G.Adj (q 1) (v 0) at hadj
    exact False.elim (hrows.2.2.2.2.1 0 hadj)
  · change G.Adj (q 1) (v 1) at hadj
    exact False.elim (hrows.2.2.2.2.1 1 hadj)
  · change G.Adj (q 1) (v 2) at hadj
    exact False.elim (hrows.2.2.2.2.1 2 hadj)
  · change G.Adj (q 1) (v 3) at hadj
    exact False.elim (hrows.2.2.2.2.1 3 hadj)
  · change G.Adj (PawEncoding.labeling p q hd 6)
      (PawEncoding.labeling p q hd 0) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 6 0 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 6 0) hh)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (q 2) (q 2) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 7)
      (PawEncoding.labeling p q hd 0) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 7 0 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 7 0) hh)
  · change G.Adj (PawEncoding.labeling p q hd 7)
      (PawEncoding.labeling p q hd 1) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 7 1 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 7 1) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 7)
      (PawEncoding.labeling p q hd 3) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 7 3 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 7 3) hh)
  · exact by decide +kernel
  · change G.Adj (PawEncoding.labeling p q hd 7)
      (PawEncoding.labeling p q hd 5) at hadj
    have hh := WeightedFifteen.adj_upper p q hd h hleaf hcenter 7 5 hadj
    exact False.elim ((by decide +kernel : ¬WeightedFifteen.upperGraph.Adj 7 5) hh)
  · exact by decide +kernel
  · change G.Adj (q 3) (q 3) at hadj
    exact False.elim (G.irrefl hadj)
  · change G.Adj (q 3) (v 0) at hadj
    exact False.elim (hrows.2.2.2.2.2 0 hadj)
  · change G.Adj (q 3) (v 1) at hadj
    exact False.elim (hrows.2.2.2.2.2 1 hadj)
  · change G.Adj (q 3) (v 2) at hadj
    exact False.elim (hrows.2.2.2.2.2 2 hadj)
  · change G.Adj (q 3) (v 3) at hadj
    exact False.elim (hrows.2.2.2.2.2 3 hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (v 0) (p.vertices 3) at hadj
    exact False.elim (hrows.2.2.2.1 0 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (v 0) (q 1) at hadj
    exact False.elim (hrows.2.2.2.2.1 0 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (v 0) (q 3) at hadj
    exact False.elim (hrows.2.2.2.2.2 0 hadj.symm)
  · change G.Adj (v 0) (v 0) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (v 1) (p.vertices 3) at hadj
    exact False.elim (hrows.2.2.2.1 1 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (v 1) (q 1) at hadj
    exact False.elim (hrows.2.2.2.2.1 1 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (v 1) (q 3) at hadj
    exact False.elim (hrows.2.2.2.2.2 1 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (v 1) (v 1) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (v 2) (p.vertices 3) at hadj
    exact False.elim (hrows.2.2.2.1 2 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (v 2) (q 1) at hadj
    exact False.elim (hrows.2.2.2.2.1 2 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (v 2) (q 3) at hadj
    exact False.elim (hrows.2.2.2.2.2 2 hadj.symm)
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (v 2) (v 2) at hadj
    exact False.elim (G.irrefl hadj)
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (v 3) (p.vertices 1) at hadj
    exact False.elim (((hrows.2.1 3).mp hadj.symm) rfl)
  · exact by decide +kernel
  · change G.Adj (v 3) (p.vertices 3) at hadj
    exact False.elim (hrows.2.2.2.1 3 hadj.symm)
  · change G.Adj (v 3) (q 0) at hadj
    exact False.elim (((hrows.2.2.1 3).mp hadj.symm) rfl)
  · change G.Adj (v 3) (q 1) at hadj
    exact False.elim (hrows.2.2.2.2.1 3 hadj.symm)
  · exact by decide +kernel
  · change G.Adj (v 3) (q 3) at hadj
    exact False.elim (hrows.2.2.2.2.2 3 hadj.symm)
  · exact by decide +kernel
  · exact by decide +kernel
  · exact by decide +kernel
  · change G.Adj (v 3) (v 3) at hadj
    exact False.elim (G.irrefl hadj)

end Erdos577.WeightedFifteen.DenseModel
