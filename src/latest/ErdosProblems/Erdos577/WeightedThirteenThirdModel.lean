import ErdosProblems.Erdos577.WeightedThirteenDenseModel
import ErdosProblems.Erdos577.WeightedThirteenLowTerminals

/-! The positive sixteen-vertex core for a nonuniversal low row in pattern (13). -/

namespace Erdos577.WeightedThirteen.ThirdModel

open Finset

def low (second : Bool) : Fin 16 := if second then 7 else 5

def own (second : Bool) : Fin 16 := if second then 2 else 3

def pairs (second : Bool) : Finset (Fin 16 × Fin 16) := {
    (0, 1), (0, 4), (1, 2), (1, 3), (1, 8), (1, 9),
    (1, 10), (2, 3), (2, 4), (2, 6), (2, 7), (2, 8),
    (2, 9), (2, 10), (2, 11), (3, 4), (3, 5), (3, 6),
    (3, 8), (3, 9), (3, 10), (3, 11), (4, 5), (4, 7),
    (5, 6), (5, 8), (5, 9), (5, 10), (6, 7), (8, 9),
    (8, 10), (8, 11), (9, 10), (9, 11), (10, 11),
    (4, 6), (12, 13), (13, 14), (14, 15), (12, 15),
    (low second, 12), (low second, 13), (low second, 14)}

def graph (second : Bool) : SimpleGraph (Fin 16) :=
  SimpleGraph.fromRel fun i j ↦ (i, j) ∈ pairs second

instance (second : Bool) : DecidableRel (graph second).Adj := inferInstanceAs (DecidableRel
  (SimpleGraph.fromRel (fun i j : Fin 16 ↦ (i, j) ∈ pairs second)).Adj)

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def labeling (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (w : Quadrilateral G) (hw : Disjoint ((p.support ∪ q.support) ∪ v.support) w.support) :
    Fin 16 ↪ V :=
  joinTuples (WeightedFifteen.twoBlockLabeling p q hd v hv) w.toEmbedding (by
    change Disjoint (univ.image (WeightedFifteen.twoBlockLabeling p q hd v hv)) w.support
    rw [WeightedFifteen.twoBlockLabeling_image]
    exact hw)

lemma labeling_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (w : Quadrilateral G) (hw : Disjoint ((p.support ∪ q.support) ∪ v.support) w.support) :
    univ.image (labeling p q hd v hv w hw) =
      ((p.support ∪ q.support) ∪ v.support) ∪ w.support := by
  change tupleSupport (labeling p q hd v hv w hw) = _
  rw [labeling, tupleSupport_joinTuples]
  change univ.image (WeightedFifteen.twoBlockLabeling p q hd v hv) ∪ w.support = _
  rw [WeightedFifteen.twoBlockLabeling_image]

variable [DecidableRel G.Adj]

def copy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern13 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    (w : Quadrilateral G) (hw : Disjoint ((p.support ∪ q.support) ∪ v.support) w.support)
    (hdiag : G.Adj (q 0) (q 2)) (second : Bool)
    (hrow : ∀ j : Fin 4, G.Adj (q (lowIndex second)) (w j) ↔ j ≠ 3) :
    (graph second).Copy G := by
  let e := labeling p q hd v hv w hw
  have hpos (a : Fin 16 × Fin 16) (ha : a ∈ pairs second) : G.Adj (e a.1) (e a.2) := by
    simp only [pairs, mem_insert, mem_singleton] at ha
    rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha |
      ha | ha | ha | ha | ha | ha | ha | ha | ha | ha |
      ha | ha | ha | ha | ha | ha | ha | ha | ha | ha |
      ha | ha | ha | ha | ha | ha | ha | ha | ha | ha |
      ha | ha | ha
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 0)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 1)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 0 1)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 0)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 4)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 0 4)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 1)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 2)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 1 2)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 1)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 3)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 1 3)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 1)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 8)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 1 8)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 1)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 9)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 1 9)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 1)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 10)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 1 10)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 2)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 3)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 2 3)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 2)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 4)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 2 4)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 2)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 6)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 2 6)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 2)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 7)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 2 7)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 2)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 8)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 2 8)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 2)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 9)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 2 9)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 2)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 10)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 2 10)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 2)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 11)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 2 11)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 3)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 4)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 3 4)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 3)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 5)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 3 5)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 3)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 6)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 3 6)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 3)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 8)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 3 8)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 3)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 9)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 3 9)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 3)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 10)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 3 10)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 3)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 11)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 3 11)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 4)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 5)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 4 5)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 4)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 7)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 4 7)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 5)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 6)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 5 6)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 5)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 8)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 5 8)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 5)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 9)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 5 9)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 5)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 10)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 5 10)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 6)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 7)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 6 7)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 8)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 9)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 8 9)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 8)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 10)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 8 10)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 8)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 11)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 8 11)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 9)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 10)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 9 10)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 9)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 11)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 9 11)
    · cases ha
      change G.Adj (WeightedFifteen.twoBlockLabeling p q hd v hv 10)
        (WeightedFifteen.twoBlockLabeling p q hd v hv 11)
      exact (DenseModel.copy p q hd h v hv hcl hrows).toHom.map_rel'
        (by decide +kernel : DenseModel.graph.Adj 10 11)
    · cases ha
      exact hdiag
    · cases ha
      exact w.adjacent 0
    · cases ha
      exact w.adjacent 1
    · cases ha
      exact w.adjacent 2
    · cases ha
      exact (w.adjacent 3).symm
    · cases ha
      cases second <;> exact (hrow 0).mpr (by decide)
    · cases ha
      cases second <;> exact (hrow 1).mpr (by decide)
    · cases ha
      cases second <;> exact (hrow 2).mpr (by decide)
  refine ⟨⟨e, ?_⟩, e.injective⟩
  intro i j hij
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hij with ⟨_, hij | hji⟩
  · exact hpos (i, j) hij
  · exact (hpos (j, i) hji).symm

end Erdos577.WeightedThirteen.ThirdModel
