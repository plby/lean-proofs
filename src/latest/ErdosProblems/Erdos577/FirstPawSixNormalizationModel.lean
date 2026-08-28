import ErdosProblems.Erdos577.FirstPawSixCaseModel

/-! Explicit local exchanges turn source case (25) into (24), and (26) into (23). -/

namespace Erdos577.FirstPawSix.NormalizationModel

open Finset

def source (second : Bool) : Fin 5 := if second then 4 else 3

def target (second : Bool) : Fin 5 := if second then 1 else 2

def pawTuple (second : Bool) : Fin 4 ↪ Fin 8 :=
  ⟨if second then ![3, 1, 5, 0] else ![3, 1, 6, 7], by cases second <;> decide +kernel⟩

def quadTuple (second : Bool) : Fin 4 ↪ Fin 8 :=
  ⟨if second then ![4, 2, 6, 7] else ![4, 2, 5, 0], by cases second <;> decide +kernel⟩

def paw (second : Bool) : Paw (CaseModel.graph (source second)) where
  vertices := pawTuple second
  pendant := by cases second <;> decide +kernel
  edge12 := by cases second <;> decide +kernel
  edge13 := by cases second <;> decide +kernel
  edge23 := by cases second <;> decide +kernel

def quad (second : Bool) : Quadrilateral (CaseModel.graph (source second)) :=
  Quadrilateral.ofEdges (quadTuple second) (by cases second <;> decide +kernel)

def chain (second : Bool) : LocalChain (CaseModel.graph (source second)) univ where
  terminal := (paw second).leaf
  triangle := (paw second).triangle
  block := (quad second).support
  triangle_clique := (paw second).triangle_clique
  terminal_not_mem := (paw second).leaf_not_mem_triangle
  quad := ⟨quad second, rfl⟩
  disjoint := by cases second <;> decide +kernel
  cover := by cases second <;> decide +kernel

lemma block_score (second : Bool) :
    edgeCount (CaseModel.graph (source second)) (chain second).block = 5 := by
  cases second <;> decide +kernel

lemma only_first (second : Bool) : PawBlock.OnlyFirst (quad second) := by
  unfold PawBlock.OnlyFirst
  cases second <;> decide +kernel

lemma exact_rows (second : Bool) :
    PawBlock.ExactRows (paw second) (quad second) (caseRows (target second)) := by
  unfold PawBlock.ExactRows
  cases second <;> decide +kernel

end Erdos577.FirstPawSix.NormalizationModel
