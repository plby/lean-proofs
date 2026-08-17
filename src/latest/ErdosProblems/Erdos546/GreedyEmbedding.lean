/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos546.BoundedDegree

/-!
# The exact dyadic bounded-degree sparse-pair lemma

This file specializes the greedy embedding engine to the parameters used in
the proof of Erdős Problem 546.  Cardinality loss is stated with natural
division, so the lower bound is the literal floor required by later modules.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open Finset
open SimpleGraph

/-- If the graph induced by `U` omits a graph of maximum degree at most `D`,
then `U` contains a disjoint balanced pair of the exact dyadic size used in
the sparsification argument, with cross-density at most `2⁻⁽Q⁺³⁾`.

The assumptions `15 ≤ Q` and `1 ≤ D` are retained in this local interface
because this is the form consumed by the exact sparsification theorem. -/
theorem exists_large_pairSparse_of_not_isContained_induce
    {Q D f N : ℕ} (hQ : 15 ≤ Q) (_hD : 1 ≤ D)
    (F : SimpleGraph (Fin f)) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N))
    (hdeg : F.maxDegree ≤ D)
    (hsize : f * 2 ^ ((Q + 5) * D) ≤ U.card)
    (hfree : ¬F ⊑ H.induce (↑U : Set (Fin N))) :
    ∃ A B : Finset (Fin N),
      A ⊆ U ∧ B ⊆ U ∧ Disjoint A B ∧ A.card = B.card ∧
      U.card / 2 ^ ((Q + 5) * D) ≤ A.card ∧
      PairSparse (Q + 3) H A B := by
  classical
  let M := 2 ^ ((Q + 5) * D)
  let s := U.card / M
  have hMpos : 0 < M := by
    simp [M]
  have hfs : f ≤ s := by
    apply (Nat.le_div_iff_mul_le hMpos).2
    simpa [s, M] using hsize
  have hL : 2 ≤ 2 ^ (Q + 4) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (Q + 4) := Nat.pow_le_pow_right (by omega) (by omega)
  have hKL : 2 * 2 ^ (Q + 3) ≤ 2 ^ (Q + 4) := by
    have heq : 2 * 2 ^ (Q + 3) = 2 ^ (Q + 4) := by
      calc
        2 * 2 ^ (Q + 3) = 2 ^ (Q + 3) * 2 := Nat.mul_comm _ _
        _ = 2 ^ ((Q + 3) + 1) := (pow_succ 2 (Q + 3)).symm
        _ = 2 ^ (Q + 4) := by congr 1
    exact heq.le
  have hpow : (2 ^ (Q + 4)) ^ D ≤ M := by
    calc
      (2 ^ (Q + 4)) ^ D = 2 ^ ((Q + 4) * D) := by
        rw [pow_mul]
      _ ≤ 2 ^ ((Q + 5) * D) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right D (by omega))
      _ = M := by rfl
  have hreservoir : (2 ^ (Q + 4)) ^ D * s ≤ U.card := by
    calc
      (2 ^ (Q + 4)) ^ D * s ≤ M * s := Nat.mul_le_mul_right s hpow
      _ ≤ U.card := by
        simpa [s] using Nat.mul_div_le U.card M
  by_contra hpair
  apply hfree
  apply isContained_of_no_sparse_pair F H U hL hKL hfs hdeg hreservoir
  intro A B hAU hBU hAB hAc hBc hSparse
  apply hpair
  refine ⟨A, B, hAU, hBU, hAB, hAc.trans hBc.symm, ?_, ?_⟩
  · simpa [s] using hAc.symm.le
  · simpa only [PairSparse] using hSparse

end Erdos546
