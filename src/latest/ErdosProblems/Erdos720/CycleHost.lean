import ErdosProblems.Erdos720.GeneralAnalytic

namespace Erdos720

open Finset SimpleGraph

def cycleVertexConstant : ℕ := 8520192
def cycleRamseyEdgeConstant : ℕ :=
  4 * ((2 * cycleVertexConstant + 2) * cycleVertexConstant * cycleVertexConstant)

lemma card_cycleTemplate_le (n : ℕ) :
    Fintype.card (CycleTemplate n) ≤ cycleVertexConstant * n := by
  cases n with
  | zero => simp [CycleTemplate, TripType, outerHoleSize, innerHoleSize]
  | succ n =>
      dsimp [CycleTemplate]
      rw [card_tripType]
      · dsimp [outerHoleSize, innerHoleSize, cycleVertexConstant]
        omega
      · dsimp [outerHoleSize, innerHoleSize]
        omega

/-- For all sufficiently large `n`, there is a linearly sparse finite graph
which arrows the actual cycle graph `C_n`. -/
lemma exists_linear_cycle_ramsey_host (n : ℕ)
    (hn : 2 * cycleVertexConstant + 2 ≤ n) :
    ∃ H : SimpleGraph (Fin (Fintype.card (CycleTemplate n))),
      Nat.card H.edgeSet ≤ cycleRamseyEdgeConstant * n ∧
      Arrows H (cycleGraph n) := by
  classical
  have hnDet : 2113536 ≤ n := by
    dsimp [cycleVertexConstant] at hn
    omega
  obtain ⟨H, hEdges, hNoHole⟩ := exists_sparse_noHole_graph_linear
    cycleVertexConstant (Fintype.card (CycleTemplate n)) n (by
      dsimp [cycleVertexConstant]
      omega) hn (card_cycleTemplate_le n)
  let e : CycleTemplate n ≃ Fin (Fintype.card (CycleTemplate n)) :=
    Fintype.equivFin (CycleTemplate n)
  let HT : SimpleGraph (CycleTemplate n) := H.comap e
  have hHTNoHole : ∀ X Y : Finset (CycleTemplate n), X.card = n → Y.card = n →
      Disjoint X Y → ∃ x ∈ X, ∃ y ∈ Y, HT.Adj x y := by
    intro X Y hX hY hXY
    obtain ⟨xv, hxv, yv, hyv, hxy⟩ := hNoHole (X.map e.toEmbedding)
      (Y.map e.toEmbedding) (by simpa using hX) (by simpa using hY)
      ((Finset.disjoint_map e.toEmbedding).2 hXY)
    rcases Finset.mem_map.mp hxv with ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp hyv with ⟨y, hy, rfl⟩
    exact ⟨x, hx, y, hy, by simpa [HT] using hxy⟩
  have hTemplateArrows : Arrows HT (cycleGraph n) :=
    cycleTemplate_arrows_of_noHole hnDet HT hHTNoHole
  refine ⟨H, ?_, ?_⟩
  · simpa [cycleRamseyEdgeConstant, mul_assoc] using hEdges
  · intro R hRH
    let RT : SimpleGraph (CycleTemplate n) := R.comap e
    have hRT : RT ≤ HT := by
      intro x y hxy
      exact hRH hxy
    rcases hTemplateArrows RT hRT with hred | hblue
    · left
      exact hred.trans (Embedding.comap e.toEmbedding R).isContained
    · right
      have heq : HT \ RT = (H \ R).comap e := by
        ext x y
        simp [HT, RT]
      rw [heq] at hblue
      exact hblue.trans (Embedding.comap e.toEmbedding (H \ R)).isContained

end Erdos720
