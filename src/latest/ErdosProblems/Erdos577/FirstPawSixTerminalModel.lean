import ErdosProblems.Erdos577.FirstPawSixCaseModel

/-! Both alternate paws and their five-edge blocks in each of the three essential cases. -/

namespace Erdos577.FirstPawSix.TerminalModel

open Finset

def index (tag : Fin 3) : Fin 5 := Fin.castAdd 2 tag

def pawTuple (second : Bool) : Fin 4 ↪ Fin 8 :=
  ⟨if second then ![3, 1, 5, 0] else ![7, 4, 0, 5], by cases second <;> decide +kernel⟩

def quadTuple (second : Bool) : Fin 4 ↪ Fin 8 :=
  ⟨if second then ![2, 4, 7, 6] else ![6, 1, 3, 2], by cases second <;> decide +kernel⟩

def paw (tag : Fin 3) (second : Bool) : Paw (CaseModel.graph (index tag)) where
  vertices := pawTuple second
  pendant := by fin_cases tag <;> cases second <;> decide +kernel
  edge12 := by fin_cases tag <;> cases second <;> decide +kernel
  edge13 := by fin_cases tag <;> cases second <;> decide +kernel
  edge23 := by fin_cases tag <;> cases second <;> decide +kernel

def quad (tag : Fin 3) (second : Bool) : Quadrilateral (CaseModel.graph (index tag)) :=
  Quadrilateral.ofEdges (quadTuple second) (by fin_cases tag <;> cases second <;> decide +kernel)

def chain (tag : Fin 3) (second : Bool) : LocalChain (CaseModel.graph (index tag)) univ where
  terminal := (paw tag second).leaf
  triangle := (paw tag second).triangle
  block := (quad tag second).support
  triangle_clique := (paw tag second).triangle_clique
  terminal_not_mem := (paw tag second).leaf_not_mem_triangle
  quad := ⟨quad tag second, rfl⟩
  disjoint := by fin_cases tag <;> cases second <;> decide +kernel
  cover := by fin_cases tag <;> cases second <;> decide +kernel

lemma block_score (tag : Fin 3) (second : Bool) :
    edgeCount (CaseModel.graph (index tag)) (chain tag second).block = 5 := by
  fin_cases tag <;> cases second <;> decide +kernel

lemma other_terminal_not_mem (tag : Fin 3) (second : Bool) :
    (if second then 7 else 3 : Fin 8) ∉ (paw tag second).support := by
  fin_cases tag <;> cases second <;> decide +kernel

end Erdos577.FirstPawSix.TerminalModel
