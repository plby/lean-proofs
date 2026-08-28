import ErdosProblems.Erdos577.FirstPawPatterns
import ErdosProblems.Erdos577.PawDiagonalCopy
import ErdosProblems.Erdos577.PawCopy
import ErdosProblems.Erdos577.QuadScores

/-! The exact eighteen-edge positive core for first-paw pattern (7). -/

namespace Erdos577.FirstPawSeven

open Finset

def graph : SimpleGraph (Fin 8) := PawModel.graph 1 22385

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (PawModel.graph 1 22385).Adj)

def weightSet : Finset (Fin 8) := {0, 7, 5, 2}

def terminalSet : Finset (Fin 8) := {0, 7}

lemma weightSet_card : weightSet.card = 4 := by decide +kernel

lemma inside_weight : contacts graph weightSet univ = 13 := by decide +kernel

def alternatePaw : Paw graph where
  vertices := ⟨![7, 6, 5, 2], by decide +kernel⟩
  pendant := by decide +kernel
  edge12 := by decide +kernel
  edge13 := by decide +kernel
  edge23 := by decide +kernel

def alternateLocal : LocalChain graph univ where
  terminal := alternatePaw.leaf
  triangle := alternatePaw.triangle
  block := {0, 1, 3, 4}
  triangle_clique := alternatePaw.triangle_clique
  terminal_not_mem := alternatePaw.leaf_not_mem_triangle
  quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  disjoint := by decide +kernel
  cover := by decide +kernel

lemma alternate_score : edgeCount graph alternateLocal.block = 5 := by decide +kernel

lemma original_leaf_not_alternate : (0 : Fin 8) ∉ alternatePaw.support := by decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def coreCopy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern7 p q) : graph.Copy G :=
  PawEncoding.copyWithDiagonalOfRows p q hd 1
    (PawEncoding.first_diagonal_submask q h.1.1) 22385 (by
      intro i j hij
      have he : ∀ i j : Fin 4, (22385 : ℕ).testBit (4 * i.val + j.val) =
          ((![1, 7, 7, 5] : Fin 4 → ℕ) i).testBit j.val := by decide +kernel
      exact (h.2 i j).mpr (by rw [← he]; exact hij))

lemma coreCopy_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern7 p q) :
    univ.image (coreCopy p q hd h) = p.support ∪ q.support := PawEncoding.labeling_image p q hd

lemma old_score (p : Paw G) (q : Quadrilateral G) (h : PawBlock.Pattern7 p q) :
    edgeCount G q.support = 5 := by
  rw [q.edgeCount_eq, if_pos h.1.1, if_neg h.1.2]

end Erdos577.FirstPawSeven
