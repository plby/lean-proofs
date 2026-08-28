import ErdosProblems.Erdos577.WeightedThirteenDenseModel

/-! Thirteen explicit path-and-two-cycle rows for the third block in pattern (13). -/

namespace Erdos577.WeightedThirteen.DenseModel.FinalTable

open Finset

def terminal : Fin 13 → Fin 12 := ![0, 0, 0, 0, 0, 0, 7, 7, 7, 7, 5, 5, 5]

def triple : Fin 13 → Fin 3 → Fin 12 :=
  ![![9, 1, 10],
    ![9, 3, 5],
    ![9, 2, 7],
    ![10, 3, 5],
    ![10, 2, 7],
    ![5, 6, 7],
    ![0, 4, 5],
    ![0, 1, 9],
    ![0, 1, 10],
    ![9, 11, 10],
    ![0, 4, 7],
    ![0, 1, 9],
    ![0, 1, 10]]

def firstBlock : Fin 13 → Finset (Fin 12) :=
  ![{2, 3, 8, 11},
    {1, 8, 11, 10},
    {1, 8, 11, 10},
    {1, 8, 11, 9},
    {1, 8, 11, 9},
    {1, 2, 4, 3},
    {1, 2, 6, 3},
    {2, 4, 3, 6},
    {2, 4, 3, 6},
    {0, 1, 2, 4},
    {1, 2, 6, 3},
    {2, 4, 7, 6},
    {2, 4, 7, 6}]

def secondBlock : Fin 13 → Finset (Fin 12) :=
  ![{4, 5, 6, 7},
    {2, 4, 7, 6},
    {3, 4, 5, 6},
    {2, 4, 7, 6},
    {3, 4, 5, 6},
    {8, 9, 10, 11},
    {8, 9, 10, 11},
    {5, 8, 11, 10},
    {5, 8, 11, 9},
    {3, 6, 5, 8},
    {8, 9, 10, 11},
    {3, 8, 10, 11},
    {3, 8, 9, 11}]

def partition (tag : Fin 13) : LocalPathPartition graph (univ \ secondBlock tag) where
  terminal := terminal tag
  triple := ⟨triple tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := firstBlock tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

lemma second_quad (tag : Fin 13) : QuadOn graph (secondBlock tag) :=
  QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel) (by fin_cases tag <;> decide +kernel)

def fourSet : Finset (Fin 12) := {9, 10, 5, 7}

lemma endpoint_coverage (y z : Fin 12) (hy : y ∈ fourSet) (hz : z ∈ fourSet) (hyz : y ≠ z) :
    ∃ tag : Fin 13, terminal tag = 0 ∧
      ((triple tag 0 = y ∧ triple tag 2 = z) ∨ (triple tag 0 = z ∧ triple tag 2 = y)) := by
  have hall : ∀ y ∈ fourSet, ∀ z ∈ fourSet, y ≠ z →
      ∃ tag : Fin 13, terminal tag = 0 ∧
        ((triple tag 0 = y ∧ triple tag 2 = z) ∨
          (triple tag 0 = z ∧ triple tag 2 = y)) := by decide +kernel
  exact hall y hy z hz hyz

end Erdos577.WeightedThirteen.DenseModel.FinalTable
