import ErdosProblems.Erdos577.WeightedFourteenDenseTerminals
import ErdosProblems.Erdos577.WeightedFifteenDenseFactors

/-! Positive twelve-vertex copies for each of the three forced triangle rows. -/

namespace Erdos577.WeightedFourteen.Dense.Model

open Finset

def specialVertex : Fin 3 → Fin 12 := ![1, 2, 3]

def basePairs : Finset (Fin 12 × Fin 12) := {
    (0, 1), (0, 4), (0, 6), (0, 8), (0, 10), (1, 2),
    (1, 3), (1, 4), (1, 6), (1, 8), (1, 10), (2, 3),
    (2, 4), (2, 6), (2, 7), (2, 8), (2, 10), (3, 4),
    (3, 6), (3, 8), (3, 10), (4, 5), (4, 7), (5, 6),
    (5, 8), (5, 10), (6, 7), (7, 8), (7, 10), (8, 9),
    (8, 10), (8, 11), (9, 10), (10, 11)}

def pairs (special : Fin 3) : Finset (Fin 12 × Fin 12) :=
  insert (specialVertex special, 11) basePairs

def graph (special : Fin 3) : SimpleGraph (Fin 12) :=
  SimpleGraph.fromRel fun i j ↦ (i, j) ∈ pairs special

instance (special : Fin 3) : DecidableRel (graph special).Adj :=
  inferInstanceAs (DecidableRel
    (SimpleGraph.fromRel (fun i j : Fin 12 ↦ (i, j) ∈ pairs special)).Adj)

def terminalIndex : Fin 4 → Fin 12 := ![0, 5, 7, 9]

def terminalSet : Finset (Fin 12) := {0, 5, 7, 9}

lemma terminalSet_card : terminalSet.card = 4 := by decide +kernel

lemma terminalSet_eq : terminalSet = univ.image terminalIndex := by decide +kernel

lemma terminalIndex_injective : Function.Injective terminalIndex := by decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def copy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q)
    (hcenter : ∀ j : Fin 4, G.Adj p.center (q j) ↔ (5 : ℕ).testBit j.val = true)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (special : Fin 3) (hrows : Rows p q v special) : (graph special).Copy G := by
  let e := WeightedFifteen.twoBlockLabeling p q hd v hv
  have hpHigh (i j : Fin 4) (hj : j = 0 ∨ j = 2) : G.Adj (p.vertices i) (v j) := by
    apply (hrows.2.1 i j).mpr
    have hh : ∀ special : Fin 3, ∀ i j : Fin 4, (j = 0 ∨ j = 2) →
        (pawRows special i).testBit j.val = true := by decide +kernel
    exact hh special i j hj
  have hpos (a : Fin 12 × Fin 12) (ha : a ∈ pairs special) : G.Adj (e a.1) (e a.2) := by
    rcases mem_insert.mp ha with ha | ha
    · cases ha
      fin_cases special
      · exact (hrows.2.1 1 3).mpr (by decide)
      · exact (hrows.2.1 2 3).mpr (by decide)
      · exact (hrows.2.1 3 3).mpr (by decide)
    · simp only [basePairs, mem_insert, mem_singleton] at ha
      rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha |
        ha | ha | ha | ha | ha | ha | ha | ha | ha | ha |
        ha | ha | ha | ha | ha | ha | ha | ha | ha | ha |
        ha | ha | ha | ha
      · cases ha
        exact p.pendant
      · cases ha
        exact (h.2.1 0).mpr (by decide)
      · cases ha
        exact (h.2.1 2).mpr (by decide)
      · cases ha
        exact hpHigh 0 0 (Or.inl rfl)
      · cases ha
        exact hpHigh 0 2 (Or.inr rfl)
      · cases ha
        exact p.edge12
      · cases ha
        exact p.edge13
      · cases ha
        exact (hcenter 0).mpr (by decide)
      · cases ha
        exact (hcenter 2).mpr (by decide)
      · cases ha
        exact hpHigh 1 0 (Or.inl rfl)
      · cases ha
        exact hpHigh 1 2 (Or.inr rfl)
      · cases ha
        exact p.edge23
      · cases ha
        exact (h.2.2.1 0).mpr (by decide)
      · cases ha
        exact (h.2.2.1 2).mpr (by decide)
      · cases ha
        exact (h.2.2.1 3).mpr (by decide)
      · cases ha
        exact hpHigh 2 0 (Or.inl rfl)
      · cases ha
        exact hpHigh 2 2 (Or.inr rfl)
      · cases ha
        exact (h.2.2.2 0).mpr (by decide)
      · cases ha
        exact (h.2.2.2 2).mpr (by decide)
      · cases ha
        exact hpHigh 3 0 (Or.inl rfl)
      · cases ha
        exact hpHigh 3 2 (Or.inr rfl)
      · cases ha
        exact q.adjacent 0
      · cases ha
        exact (q.adjacent 3).symm
      · cases ha
        exact q.adjacent 1
      · cases ha
        exact (hrows.2.2.1 0).mpr (by decide)
      · cases ha
        exact (hrows.2.2.1 2).mpr (by decide)
      · cases ha
        exact q.adjacent 2
      · cases ha
        exact (hrows.2.2.2 0).mpr (by decide)
      · cases ha
        exact (hrows.2.2.2 2).mpr (by decide)
      · cases ha
        exact v.adjacent 0
      · cases ha
        exact hrows.1.1
      · cases ha
        exact (v.adjacent 3).symm
      · cases ha
        exact v.adjacent 1
      · cases ha
        exact v.adjacent 2
  refine ⟨⟨e, ?_⟩, e.injective⟩
  intro i j hij
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hij with ⟨_, hij | hji⟩
  · exact hpos (i, j) hij
  · exact (hpos (j, i) hji).symm

lemma copy_terminal (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q)
    (hcenter : ∀ j : Fin 4, G.Adj p.center (q j) ↔ (5 : ℕ).testBit j.val = true)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (special : Fin 3) (hrows : Rows p q v special) (tag : Fin 4) :
    copy p q hd h hcenter v hv special hrows (terminalIndex tag) = terminals p q v tag := by
  fin_cases tag <;> rfl

end Erdos577.WeightedFourteen.Dense.Model
