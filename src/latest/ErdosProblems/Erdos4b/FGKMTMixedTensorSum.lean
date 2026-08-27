/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTensorSum

/-!
# A literal sieve sum with one distinct coordinate factor

The parameter `j` counts the remaining equal factors. The distinguished
factor occurs at coordinate zero in a genuine `(j+1)`-tuple sum.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def mixedTensorSieveSum (M : ℕ) (g : ℕ → ℝ) (R j : ℕ) (H G : ℝ → ℝ) : ℝ :=
  ∑ e : Fin (j + 1) → Fin (R + 1),
    H (Real.log (e 0).val / Real.log R) *
      (∏ i : Fin j, G (Real.log (e i.succ).val / Real.log R)) *
        roughSieveWeight M g (∏ i, (e i).val)

theorem mixedTensorSieveSum_split (M R j : ℕ) (g : ℕ → ℝ) (H G : ℝ → ℝ) :
    mixedTensorSieveSum M g R j H G =
      ∑ e : Fin j → Fin (R + 1), (∏ i, G (Real.log (e i).val / Real.log R)) *
        (∑ n ∈ Finset.Icc 0 R,
          H (Real.log n / Real.log R) * roughSieveWeight M g ((∏ i, (e i).val) * n)) := by
  classical
  unfold mixedTensorSieveSum
  rw [← (Fin.consEquiv (fun _ : Fin (j + 1) => Fin (R + 1))).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum, ← sum_fin_succ_eq_sum_Icc]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [Nat.mul_comm n.val]
  ring

theorem mixedTensorSieveSum_same (M R j : ℕ) (g : ℕ → ℝ) (G : ℝ → ℝ) :
    mixedTensorSieveSum M g R j G G = tensorSieveSum M g R (j + 1) G := by
  rw [mixedTensorSieveSum_split, tensorSieveSum_succ]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.mixedTensorSieveSum_split
