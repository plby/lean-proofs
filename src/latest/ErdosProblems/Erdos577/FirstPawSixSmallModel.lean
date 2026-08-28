import ErdosProblems.Erdos577.FirstPawSixCaseUpper
import ErdosProblems.Erdos577.FirstPawSixTerminalModel
import ErdosProblems.Erdos577.LocalPathPartition

/-! The two common-triple cases (22)/(23), their inside counts, and six insertion witnesses. -/

namespace Erdos577.FirstPawSix.SmallCases

open Finset

def index (variant : Bool) : Fin 3 := if variant then 1 else 0

def caseTag (variant : Bool) : Fin 5 := TerminalModel.index (index variant)

def graph (variant : Bool) : SimpleGraph (Fin 8) := CaseModel.graph (caseTag variant)

instance (variant : Bool) : DecidableRel (graph variant).Adj :=
  inferInstanceAs (DecidableRel (CaseModel.graph (caseTag variant)).Adj)

def weightSet : Finset (Fin 8) := {7, 0, 5, 3}

def terminalSet : Finset (Fin 8) := {3, 7}

lemma weightSet_card : weightSet.card = 4 := by decide +kernel

lemma inside_weight (variant : Bool) : contacts (graph variant) weightSet univ ≤ 14 := by
  cases variant <;> decide +kernel

namespace FactorTable

def terminal : Fin 6 → Fin 8 := ![3, 3, 3, 7, 7, 7]

def triple : Fin 6 → Fin 3 → Fin 8 :=
  ![![0, 1, 7], ![0, 4, 5], ![5, 6, 7], ![0, 1, 3], ![0, 4, 5], ![5, 2, 3]]

def block : Fin 6 → Finset (Fin 8) :=
  ![{2, 4, 5, 6}, {1, 2, 6, 7}, {0, 1, 2, 4}, {2, 4, 5, 6}, {1, 3, 2, 6}, {0, 1, 6, 4}]

def partition (variant : Bool) (tag : Fin 6) : LocalPathPartition (graph variant) univ where
  terminal := terminal tag
  triple := ⟨triple tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by cases variant <;> fin_cases tag <;> decide +kernel
  edge12 := by cases variant <;> fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by cases variant <;> fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

lemma endpoint_coverage (u v w : Fin 8) (hu : u ∈ terminalSet)
    (hv : v ∈ weightSet.erase u) (hw : w ∈ weightSet.erase u) (hvw : v ≠ w) :
    ∃ tag : Fin 6, terminal tag = u ∧
      ((triple tag 0 = v ∧ triple tag 2 = w) ∨ (triple tag 0 = w ∧ triple tag 2 = v)) := by
  have hall : ∀ u v w : Fin 8, u ∈ terminalSet → v ∈ weightSet.erase u →
      w ∈ weightSet.erase u → v ≠ w → ∃ tag : Fin 6, terminal tag = u ∧
        ((triple tag 0 = v ∧ triple tag 2 = w) ∨ (triple tag 0 = w ∧ triple tag 2 = v)) := by
    decide +kernel
  exact hall u v w hu hv hw hvw

end FactorTable

end Erdos577.FirstPawSix.SmallCases
