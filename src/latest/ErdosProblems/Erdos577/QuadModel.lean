import ErdosProblems.Erdos577.DiagonalDegrees
import ErdosProblems.Erdos577.PawModel

/-! Exact adjacency on the old block, including negative diagonal information. -/

namespace Erdos577

private lemma four_distinct_cases (i j : Fin 4) (h : i ≠ j) :
    (SimpleGraph.cycleGraph 4).Adj i j ∨ j = i + 2 := by
  have hf : ∀ i j : Fin 4, i ≠ j → (SimpleGraph.cycleGraph 4).Adj i j ∨ j = i + 2 := by
    decide +kernel
  exact hf i j h

private lemma finite_quad_adj (diagonal : Fin 4) (i j : Fin 4) :
    (PawModel.graph diagonal 0).Adj (Fin.natAdd 4 i) (Fin.natAdd 4 j) ↔
      (SimpleGraph.cycleGraph 4).Adj i j ∨
        (j = i + 2 ∧ diagonal.val.testBit (i.val % 2) = true) := by
  have hf : ∀ diagonal : Fin 4, ∀ i j : Fin 4,
      (PawModel.graph diagonal 0).Adj (Fin.natAdd 4 i) (Fin.natAdd 4 j) ↔
        (SimpleGraph.cycleGraph 4).Adj i j ∨
          (j = i + 2 ∧ diagonal.val.testBit (i.val % 2) = true) := by
    decide +kernel
  exact hf diagonal i j

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Quadrilateral.adj_diagonal_iff (q : Quadrilateral G) (i j : Fin 4) :
    G.Adj (q i) (q j) ↔ (SimpleGraph.cycleGraph 4).Adj i j ∨
      (j = i + 2 ∧ (Unattached.diagonal q).val.testBit (i.val % 2) = true) := by
  constructor
  · intro hadj
    have hne : i ≠ j := fun he ↦ hadj.ne (congrArg q he)
    rcases four_distinct_cases i j hne with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      rw [h] at hadj
      exact (q.diagonal_bit_iff i).mpr hadj
  · rintro (h | ⟨rfl, h⟩)
    · exact q.toHom.map_rel' h
    · exact (q.diagonal_bit_iff i).mp h

lemma Quadrilateral.model_adj_iff (q : Quadrilateral G) (i j : Fin 4) :
    (PawModel.graph (Unattached.diagonal q) 0).Adj (Fin.natAdd 4 i) (Fin.natAdd 4 j) ↔
      G.Adj (q i) (q j) :=
  (finite_quad_adj (Unattached.diagonal q) i j).trans (q.adj_diagonal_iff i j).symm

end Erdos577
