import ErdosProblems.Erdos577.FirstPawSixCaseUpper
import ErdosProblems.Erdos577.FirstPawFourHeavy
import ErdosProblems.Erdos577.LocalPathPartition

/-! The exact case24 core, inside weight twenty, and eight explicit insertion witnesses. -/

namespace Erdos577.FirstPawSix.WeightedCase

open Finset

def graph : SimpleGraph (Fin 8) := CaseModel.graph 2

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (CaseModel.graph 2).Adj)

def vertexSet : Finset (Fin 8) := {0, 2, 3, 5, 7}

lemma inside_weight : contacts graph (FirstPawFour.weightSet false) univ +
    contacts graph (FirstPawFour.weightSet true) univ = 20 := by decide +kernel

namespace FactorTable

def terminal : Fin 8 → Fin 8 := ![0, 0, 0, 0, 0, 0, 3, 2]

def triple : Fin 8 → Fin 3 → Fin 8 :=
  ![![3, 1, 2], ![3, 1, 7], ![3, 1, 5], ![2, 6, 7],
    ![2, 6, 5], ![7, 6, 5], ![5, 6, 7], ![7, 6, 5]]

def block : Fin 8 → Finset (Fin 8) :=
  ![{4, 5, 6, 7}, {2, 4, 5, 6}, {2, 4, 7, 6}, {1, 3, 4, 5},
    {1, 3, 4, 7}, {1, 2, 3, 4}, {0, 1, 2, 4}, {0, 1, 3, 4}]

def partition (tag : Fin 8) : LocalPathPartition graph univ where
  terminal := terminal tag
  triple := ⟨triple tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

lemma endpoint_coverage (v w : Fin 8) (hv : v ∈ vertexSet.erase 0)
    (hw : w ∈ vertexSet.erase 0) (hvw : v ≠ w) :
    ∃ tag : Fin 8, terminal tag = 0 ∧
      ((triple tag 0 = v ∧ triple tag 2 = w) ∨ (triple tag 0 = w ∧ triple tag 2 = v)) := by
  have hall : ∀ v w : Fin 8, v ∈ vertexSet.erase 0 → w ∈ vertexSet.erase 0 → v ≠ w →
      ∃ tag : Fin 8, terminal tag = 0 ∧
        ((triple tag 0 = v ∧ triple tag 2 = w) ∨ (triple tag 0 = w ∧ triple tag 2 = v)) := by
    decide +kernel
  exact hall v w hv hw hvw

end FactorTable

end Erdos577.FirstPawSix.WeightedCase
