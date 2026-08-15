import ErdosProblems.Erdos250.Erdos250Arithmetic
import ErdosProblems.Erdos250.Erdos250VNormalization

open scoped BigOperators

namespace OldDecayFull

open Erdos250Arithmetic VNormalization

lemma denProd_le_pow_two_tri (n : ℕ) :
    denProd n ≤ 2 ^ (n * (n + 1) / 2) := by
  rw [denProd]
  calc
    ∏ d ∈ Finset.Icc 1 n, oddFactor d ≤
        ∏ d ∈ Finset.Icc 1 n, 2 ^ d := by
      apply Finset.prod_le_prod'
      intro d hd
      exact Nat.sub_le _ _
    _ = 2 ^ (∑ d ∈ Finset.Icc 1 n, d) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = 2 ^ (n * (n + 1) / 2) := by
      rw [VNormalization.sum_Icc_id]

end OldDecayFull
