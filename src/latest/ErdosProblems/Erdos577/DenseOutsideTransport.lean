import ErdosProblems.Erdos577.DenseOutsideModel
import ErdosProblems.Erdos577.UnattachedTransport

/-! Exact row counts and positive exchanges in the original graph. -/

namespace Erdos577.DenseOutside

open Finset Function Unattached
open scoped BigOperators

lemma terminalCount_eq_sum (m : ℕ) :
    terminalCount m = ∑ j : Fin 4, (m.testBit j.val).toNat := by
  simp [terminalCount, List.range_succ, Fin.sum_univ_succ]

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma terminalCount_encoded (c : TriangleChain G) (q : Quadrilateral G) :
    terminalCount (encoded c q).val = degreeIn G c.terminal q.support := by
  have hq : Injective (q : Fin 4 → V) := q.injective
  have hzero (j : Fin 4) : (encoded c q).val.testBit j.val =
      decide (G.Adj c.terminal (q j)) := by
    simpa only [Fin.val_zero, Nat.mul_zero, Nat.zero_add, c.remainderTuple_zero] using
      encoded_bit c q 0 j
  rw [terminalCount_eq_sum, Quadrilateral.support, degreeIn_image G _ _ _ hq]
  apply sum_congr rfl
  intro j _
  rw [hzero]
  by_cases he : G.Adj c.terminal (q j) <;> simp [he]

lemma triangleCount_encoded (c : TriangleChain G) (q : Quadrilateral G) :
    triangleCount (encoded c q).val = contacts G c.triangle q.support := by
  have hw : weightedCount (encoded c q).val =
      3 * terminalCount (encoded c q).val + triangleCount (encoded c q).val := rfl
  rw [weightedCount_encoded, terminalCount_encoded] at hw
  omega

lemma Positive.chain_outcome (c : TriangleChain G) (q : Quadrilateral G)
    (hd : Disjoint c.remainder q.support) (h : Positive (diagonal q) (encoded c q).val) :
    LocalFactor G (c.remainder ∪ q.support) ∨
      StrictImprovement G (c.remainder ∪ q.support) (edgeCount G q.support) := by
  rcases h with h | h
  · left
    have hg := h.image (modelCopy c q hd)
    rw [modelCopy_image] at hg
    exact hg
  · right
    have hg := h.image (modelCopy c q hd)
    rw [modelCopy_image, oldEdges_diagonal] at hg
    exact hg

end Erdos577.DenseOutside
