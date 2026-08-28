import ErdosProblems.Erdos577.FirstPawPatterns
import ErdosProblems.Erdos577.PawDiagonalCopy
import ErdosProblems.Erdos577.PawCopy
import ErdosProblems.Erdos577.QuadScores

/-! Pattern (8)'s exact core keeps the optional second diagonal. -/

namespace Erdos577.FirstPawEight

open Finset

def graph (diagonal : Fin 4) : SimpleGraph (Fin 8) := PawModel.graph diagonal 4081

instance (diagonal : Fin 4) : DecidableRel (graph diagonal).Adj :=
  inferInstanceAs (DecidableRel (PawModel.graph diagonal 4081).Adj)

def weightSet : Finset (Fin 8) := {0, 3, 5, 7}

def terminalSet : Finset (Fin 8) := {0, 3}

lemma weightSet_card : weightSet.card = 4 := by decide +kernel

lemma inside_weight (diagonal : Fin 4) : contacts (graph diagonal) weightSet univ ≤ 14 := by
  fin_cases diagonal <;> decide +kernel

def permutation : Equiv.Perm (Fin 8) where
  toFun := ![3, 1, 4, 0, 2, 5, 6, 7]
  invFun := ![3, 1, 4, 0, 2, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

lemma permutation_adj (diagonal : Fin 4) (hd : diagonal = 1 ∨ diagonal = 3) (i j : Fin 8) :
    (graph diagonal).Adj (permutation i) (permutation j) ↔ (graph diagonal).Adj i j := by
  have hh : ∀ d : Fin 4, (d = 1 ∨ d = 3) → ∀ i j : Fin 8,
      (graph d).Adj (permutation i) (permutation j) ↔ (graph d).Adj i j := by decide +kernel
  exact hh diagonal hd i j

lemma permutation_weightSet : weightSet.image permutation = weightSet := by decide +kernel

def alternatePaw (diagonal : Fin 4) : Paw (graph diagonal) where
  vertices := ⟨![3, 1, 4, 0], by decide +kernel⟩
  pendant := by fin_cases diagonal <;> decide +kernel
  edge12 := by fin_cases diagonal <;> decide +kernel
  edge13 := by fin_cases diagonal <;> decide +kernel
  edge23 := by fin_cases diagonal <;> decide +kernel

def alternateQuad (diagonal : Fin 4) : Quadrilateral (graph diagonal) :=
  Quadrilateral.ofVertices 2 5 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by fin_cases diagonal <;> decide +kernel) (by fin_cases diagonal <;> decide +kernel)
    (by fin_cases diagonal <;> decide +kernel) (by fin_cases diagonal <;> decide +kernel)

def alternateLocal (diagonal : Fin 4) : LocalChain (graph diagonal) univ where
  terminal := (alternatePaw diagonal).leaf
  triangle := (alternatePaw diagonal).triangle
  block := (alternateQuad diagonal).support
  triangle_clique := (alternatePaw diagonal).triangle_clique
  terminal_not_mem := (alternatePaw diagonal).leaf_not_mem_triangle
  quad := ⟨alternateQuad diagonal, rfl⟩
  disjoint := by fin_cases diagonal <;> decide +kernel
  cover := by fin_cases diagonal <;> decide +kernel

lemma alternate_score (diagonal : Fin 4) (hd : diagonal = 1 ∨ diagonal = 3) :
    edgeCount (graph diagonal) (alternateLocal diagonal).block = Unattached.oldEdges diagonal := by
  rcases hd with rfl | rfl <;> decide +kernel

lemma alternate_pattern (diagonal : Fin 4) (hd : diagonal = 1 ∨ diagonal = 3) :
    PawBlock.Pattern8 (alternatePaw diagonal) (alternateQuad diagonal) := by
  rcases hd with rfl | rfl <;>
    unfold PawBlock.Pattern8 PawBlock.ExactRows <;> decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma diagonal_cases (q : Quadrilateral G) (h : G.Adj (q 0) (q 2)) :
    Unattached.diagonal q = 1 ∨ Unattached.diagonal q = 3 := by
  have hb := (Unattached.diagonal_first q).mpr h
  have hh : ∀ d : Fin 4, d.val.testBit 0 = true → d = 1 ∨ d = 3 := by decide +kernel
  exact hh _ hb

def coreCopy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) : (graph (Unattached.diagonal q)).Copy G :=
  PawEncoding.copyWithDiagonalOfRows p q hd (Unattached.diagonal q) (Nat.and_self _) 4081 (by
    intro i j hij
    have he : ∀ i j : Fin 4, (4081 : ℕ).testBit (4 * i.val + j.val) =
        ((![1, 15, 15, 0] : Fin 4 → ℕ) i).testBit j.val := by decide +kernel
    exact (h.2 i j).mpr (by rw [← he]; exact hij))

lemma coreCopy_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) :
    univ.image (coreCopy p q hd h) = p.support ∪ q.support := PawEncoding.labeling_image p q hd

end Erdos577.FirstPawEight
