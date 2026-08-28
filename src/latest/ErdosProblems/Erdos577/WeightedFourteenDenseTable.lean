import ErdosProblems.Erdos577.WeightedFourteenDenseModel

/-! Twelve explicit insertion rows for each of the three forced positive graphs. -/

namespace Erdos577.WeightedFourteen.Dense.Model.FinalTable

open Finset

def inserted : Fin 12 → Fin 12 :=
  ![0, 0, 0, 5, 5, 5, 7, 7, 7, 9, 9, 9]

def triple : Fin 12 → Fin 3 → Fin 12 :=
  ![![5, 4, 7],
    ![5, 8, 9],
    ![7, 8, 9],
    ![0, 4, 7],
    ![0, 8, 9],
    ![7, 8, 9],
    ![0, 4, 5],
    ![0, 8, 9],
    ![5, 8, 9],
    ![0, 8, 5],
    ![0, 8, 7],
    ![5, 8, 7]]

def firstBlock : Fin 3 → Fin 12 → Finset (Fin 12) :=
  ![
    ![{2, 1, 3, 6},
      {1, 2, 10, 11},
      {1, 2, 10, 11},
      {2, 1, 3, 6},
      {1, 2, 10, 11},
      {1, 2, 10, 11},
      {2, 1, 3, 6},
      {1, 2, 10, 11},
      {1, 2, 10, 11},
      {1, 2, 10, 11},
      {1, 2, 10, 11},
      {1, 2, 10, 11}],
    ![{2, 1, 3, 6},
      {2, 1, 10, 11},
      {2, 1, 10, 11},
      {2, 1, 3, 6},
      {2, 1, 10, 11},
      {2, 1, 10, 11},
      {2, 1, 3, 6},
      {2, 1, 10, 11},
      {2, 1, 10, 11},
      {2, 1, 10, 11},
      {2, 1, 10, 11},
      {2, 1, 10, 11}],
    ![{2, 1, 3, 6},
      {3, 1, 10, 11},
      {3, 1, 10, 11},
      {2, 1, 3, 6},
      {3, 1, 10, 11},
      {3, 1, 10, 11},
      {2, 1, 3, 6},
      {3, 1, 10, 11},
      {3, 1, 10, 11},
      {3, 1, 10, 11},
      {3, 1, 10, 11},
      {3, 1, 10, 11}]]

def secondBlock : Fin 3 → Fin 12 → Finset (Fin 12) :=
  ![
    ![{8, 9, 10, 11},
      {7, 4, 3, 6},
      {5, 4, 3, 6},
      {8, 9, 10, 11},
      {7, 4, 3, 6},
      {0, 4, 3, 6},
      {8, 9, 10, 11},
      {5, 4, 3, 6},
      {0, 4, 3, 6},
      {7, 4, 3, 6},
      {5, 4, 3, 6},
      {0, 4, 3, 6}],
    ![{8, 9, 10, 11},
      {7, 4, 3, 6},
      {5, 4, 3, 6},
      {8, 9, 10, 11},
      {7, 4, 3, 6},
      {0, 4, 3, 6},
      {8, 9, 10, 11},
      {5, 4, 3, 6},
      {0, 4, 3, 6},
      {7, 4, 3, 6},
      {5, 4, 3, 6},
      {0, 4, 3, 6}],
    ![{8, 9, 10, 11},
      {7, 4, 2, 6},
      {5, 4, 2, 6},
      {8, 9, 10, 11},
      {7, 4, 2, 6},
      {0, 4, 2, 6},
      {8, 9, 10, 11},
      {5, 4, 2, 6},
      {0, 4, 2, 6},
      {7, 4, 2, 6},
      {5, 4, 2, 6},
      {0, 4, 2, 6}]]

def partition (special : Fin 3) (tag : Fin 12) :
    LocalPathPartition (graph special) (univ \ secondBlock special tag) where
  terminal := inserted tag
  triple := ⟨triple tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases special <;> fin_cases tag <;> decide +kernel
  edge12 := by fin_cases special <;> fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := firstBlock special tag
  quad := QuadOn.of_degreeIn (by fin_cases special <;> fin_cases tag <;> decide +kernel)
    (by fin_cases special <;> fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases special <;> fin_cases tag <;> decide +kernel
  cover := by fin_cases special <;> fin_cases tag <;> decide +kernel

lemma second_quad (special : Fin 3) (tag : Fin 12) :
    QuadOn (graph special) (secondBlock special tag) :=
  QuadOn.of_degreeIn (by fin_cases special <;> fin_cases tag <;> decide +kernel)
    (by fin_cases special <;> fin_cases tag <;> decide +kernel)

lemma endpoint_coverage (x y z : Fin 12) (hx : x ∈ terminalSet) (hy : y ∈ terminalSet)
    (hz : z ∈ terminalSet) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ tag : Fin 12, inserted tag = x ∧
      ((triple tag 0 = y ∧ triple tag 2 = z) ∨ (triple tag 0 = z ∧ triple tag 2 = y)) := by
  have hall : ∀ x ∈ terminalSet, ∀ y ∈ terminalSet, ∀ z ∈ terminalSet,
      x ≠ y → x ≠ z → y ≠ z →
      ∃ tag : Fin 12, inserted tag = x ∧
        ((triple tag 0 = y ∧ triple tag 2 = z) ∨
          (triple tag 0 = z ∧ triple tag 2 = y)) := by decide +kernel
  exact hall x hx y hy z hz hxy hxz hyz

end Erdos577.WeightedFourteen.Dense.Model.FinalTable
