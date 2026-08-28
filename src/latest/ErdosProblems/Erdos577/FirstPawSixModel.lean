import ErdosProblems.Erdos577.FirstPawPatterns
import ErdosProblems.Erdos577.PawDiagonalCopy
import ErdosProblems.Erdos577.PawCopy
import ErdosProblems.Erdos577.QuadScores

/-! The ten allowed contacts and five essential contacts
in the first reduction of pattern (6). -/

namespace Erdos577.FirstPawSix

open Finset

def row : Fin 10 → Fin 4 := ![0, 0, 1, 1, 1, 1, 2, 2, 2, 3]

def column : Fin 10 → Fin 4 := ![0, 1, 0, 1, 2, 3, 0, 1, 2, 0]

def critical : Fin 5 → Fin 10 := ![2, 9, 7, 8, 0]

def upperGraph : SimpleGraph (Fin 8) := PawModel.graph 1 6131

instance : DecidableRel upperGraph.Adj := inferInstanceAs (DecidableRel (PawModel.graph 1 6131).Adj)

def essentialGraph : SimpleGraph (Fin 8) := PawModel.graph 1 5649

instance : DecidableRel essentialGraph.Adj :=
  inferInstanceAs (DecidableRel (PawModel.graph 1 5649).Adj)

def essentialPaw : Paw essentialGraph where
  vertices := ⟨![7, 6, 2, 5], by decide +kernel⟩
  pendant := by decide +kernel
  edge12 := by decide +kernel
  edge13 := by decide +kernel
  edge23 := by decide +kernel

def essentialQuad : Quadrilateral essentialGraph :=
  Quadrilateral.ofEdges ⟨![4, 0, 1, 3], by decide +kernel⟩ (by decide +kernel)

def essentialLocal : LocalChain essentialGraph univ where
  terminal := essentialPaw.leaf
  triangle := essentialPaw.triangle
  block := essentialQuad.support
  triangle_clique := essentialPaw.triangle_clique
  terminal_not_mem := essentialPaw.leaf_not_mem_triangle
  quad := ⟨essentialQuad, rfl⟩
  disjoint := by decide +kernel
  cover := by decide +kernel

lemma essential_score : edgeCount essentialGraph essentialLocal.block = 5 := by decide +kernel

lemma essential_first_diagonal : essentialGraph.Adj (essentialQuad 0) (essentialQuad 2) := by
  decide +kernel

lemma essential_low_absent : ¬upperGraph.Adj (essentialQuad 1) (essentialQuad 3) := by
  decide +kernel

lemma essential_high_rows (j : Fin 4)
    (h : upperGraph.Adj (essentialPaw.vertices 0) (essentialQuad j) ∨
      upperGraph.Adj (essentialPaw.vertices 1) (essentialQuad j)) : j = 0 ∨ j = 2 := by
  have hall : ∀ j : Fin 4,
      (upperGraph.Adj (essentialPaw.vertices 0) (essentialQuad j) ∨
        upperGraph.Adj (essentialPaw.vertices 1) (essentialQuad j)) → j = 0 ∨ j = 2 := by
    decide +kernel
  exact hall j h

lemma essential_noncentral_two (j : Fin 4)
    (h : upperGraph.Adj (essentialPaw.vertices 2) (essentialQuad j)) : j ≠ 1 := by
  have hall : ∀ j : Fin 4,
      upperGraph.Adj (essentialPaw.vertices 2) (essentialQuad j) → j ≠ 1 := by decide +kernel
  exact hall j h

lemma essential_noncentral_three (j : Fin 4)
    (h : upperGraph.Adj (essentialPaw.vertices 3) (essentialQuad j)) : j ≠ 3 := by
  have hall : ∀ j : Fin 4,
      upperGraph.Adj (essentialPaw.vertices 3) (essentialQuad j) → j ≠ 3 := by decide +kernel
  exact hall j h

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Essential (p : Paw G) (q : Quadrilateral G) : Prop :=
  ∀ tag : Fin 5, G.Adj (p.vertices (row (critical tag))) (q (column (critical tag)))

def essentialCopy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern6 p q) (he : Essential p q) : essentialGraph.Copy G :=
  PawEncoding.copyWithDiagonalOfRows p q hd 1
    (PawEncoding.first_diagonal_submask q h.1.1) 5649 (by
      intro i j hij
      have hall : ∀ i j : Fin 4, (5649 : ℕ).testBit (4 * i.val + j.val) = true →
          ∃ tag : Fin 5, row (critical tag) = i ∧ column (critical tag) = j := by decide +kernel
      obtain ⟨tag, rfl, rfl⟩ := hall i j hij
      exact he tag)

lemma essentialCopy_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern6 p q) (he : Essential p q) :
    univ.image (essentialCopy p q hd h he) = p.support ∪ q.support :=
  PawEncoding.labeling_image p q hd

lemma old_score (p : Paw G) (q : Quadrilateral G) (h : PawBlock.Pattern6 p q) :
    edgeCount G q.support = 5 := by
  rw [q.edgeCount_eq, if_pos h.1.1, if_neg h.1.2]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma allowed_row (p : Paw G) (q : Quadrilateral G) (h : PawBlock.Pattern6 p q)
    (i j : Fin 4) (he : G.Adj (p.vertices i) (q j)) :
    ((![3, 15, 7, 1] : Fin 4 → ℕ) i).testBit j.val = true := by
  fin_cases i
  · rcases h.2.1 j he with rfl | rfl <;> decide
  · fin_cases j <;> decide
  · have hj := h.2.2.1 j he
    fin_cases j
    · decide
    · decide
    · decide
    · exact False.elim (hj rfl)
  · rw [h.2.2.2 j he]
    decide

end Erdos577.FirstPawSix
