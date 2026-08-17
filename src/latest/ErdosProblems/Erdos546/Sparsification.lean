/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos546.GreedyEmbedding
import ErdosProblems.Erdos546.SparseInduction

/-!
# Bounded-degree sparsification

This file combines the greedy bounded-degree sparse-pair lemma with the exact
Fox--Sudakov block induction.  The result is the rounded dyadic version of the
sparsification lemma used in Sudakov's proof of Erdős Problem 546.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open Finset SimpleGraph

/-- A graph omitting a positive-order graph `F` of maximum degree at most `D`
has a large induced vertex set of ordered internal density at most `2⁻Q`.

The cardinality conclusion is division-free: the original host order is at
most `2^(8 D Q²)` times the size of the sparse set. -/
theorem exists_squareSparse_of_boundedDegree_free
    {f N Q D : ℕ} (F : SimpleGraph (Fin f)) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin N))
    (hf : 0 < f) (hQ : 15 ≤ Q) (hD : 1 ≤ D)
    (hdeg : F.maxDegree ≤ D)
    (hN : f * 2 ^ (8 * D * Q ^ 2) ≤ N)
    (hfree : ¬F ⊑ H) :
    ∃ S : Finset (Fin N), SquareSparse Q H S ∧
      N ≤ 2 ^ (8 * D * Q ^ 2) * S.card := by
  classical
  apply exists_squareSparse_of_local_sparse_pairs H hQ hD hN
  intro U hU
  have hfreeU : ¬F ⊑ H.induce (↑U : Set (Fin N)) := by
    intro hcopy
    apply hfree
    exact hcopy.trans
      (SimpleGraph.Embedding.induce (G := H) (↑U : Set (Fin N))).isContained
  obtain ⟨A, B, hAU, hBU, hAB, hcard, hlarge, hsparse⟩ :=
    exists_large_pairSparse_of_not_isContained_induce hQ hD F H U hdeg hU hfreeU
  have hMpos : 0 < 2 ^ ((Q + 5) * D) := by positivity
  have hfFloor : f ≤ U.card / 2 ^ ((Q + 5) * D) :=
    (Nat.le_div_iff_mul_le hMpos).2 hU
  have hApos : 0 < A.card := hf.trans_le (hfFloor.trans hlarge)
  exact ⟨A, B, hAU, hBU, hAB, Finset.card_pos.mp hApos,
    hcard, hlarge, hsparse⟩

end Erdos546
