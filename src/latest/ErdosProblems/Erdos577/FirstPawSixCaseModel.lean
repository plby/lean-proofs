import ErdosProblems.Erdos577.FirstPawSixCases

/-! Exact finite models for source cases (22)–(26), with their literal cross-edge masks. -/

namespace Erdos577.FirstPawSix.CaseModel

open Finset

def mask : Fin 5 → ℕ := ![6115, 2035, 5619, 5107, 6130]

def graph (tag : Fin 5) : SimpleGraph (Fin 8) := PawModel.graph 1 (mask tag)

instance (tag : Fin 5) : DecidableRel (graph tag).Adj :=
  inferInstanceAs (DecidableRel (PawModel.graph 1 (mask tag)).Adj)

lemma mask_bits (tag : Fin 5) (i j : Fin 4) :
    (mask tag).testBit (4 * i.val + j.val) = (caseRows tag i).testBit j.val := by
  have hall : ∀ tag : Fin 5, ∀ i j : Fin 4,
      (mask tag).testBit (4 * i.val + j.val) = (caseRows tag i).testBit j.val := by decide +kernel
  exact hall tag i j

lemma cross_adj (tag : Fin 5) (i j : Fin 4) :
    (graph tag).Adj (Fin.castAdd 4 i) (Fin.natAdd 4 j) ↔
      (caseRows tag i).testBit j.val = true := by
  have hall : ∀ i j : Fin 4, (graph tag).Adj (Fin.castAdd 4 i) (Fin.natAdd 4 j) ↔
      (caseRows tag i).testBit j.val = true := by fin_cases tag <;> decide +kernel
  exact hall i j

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def copy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : G.Adj (q 0) (q 2)) (tag : Fin 5) (hrows : PawBlock.ExactRows p q (caseRows tag)) :
    (graph tag).Copy G :=
  PawEncoding.copyWithDiagonalOfRows p q hd 1 (PawEncoding.first_diagonal_submask q hdiag)
    ⟨mask tag, by fin_cases tag <;> decide +kernel⟩ (by
      intro i j hij
      exact (hrows i j).mpr ((mask_bits tag i j) ▸ hij))

lemma copy_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : G.Adj (q 0) (q 2)) (tag : Fin 5) (hrows : PawBlock.ExactRows p q (caseRows tag)) :
    univ.image (copy p q hd hdiag tag hrows) = p.support ∪ q.support :=
  PawEncoding.labeling_image p q hd

end Erdos577.FirstPawSix.CaseModel
