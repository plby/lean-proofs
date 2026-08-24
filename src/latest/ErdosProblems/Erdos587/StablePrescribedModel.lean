import ErdosProblems.Erdos587.UniformHighFold
import ErdosProblems.Erdos587.HighFoldStability
import ErdosProblems.Erdos587.PrescribedRank

/-!
Stable rank-two models at a prescribed dyadic scale, constructed directly
from an interval input. All remaining hypotheses are explicit numerical
budgets; no structural or doubling hypothesis is assumed of the input set.
-/

open scoped Pointwise
open Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem dyadicSumsetWithZero_succ (A : Finset ℤ) (k : ℕ) :
    dyadicSumsetWithZero A (k + 1) = dyadicSumsetWithZero A k + dyadicSumsetWithZero A k := by
  simp only [dyadicSumsetWithZero, pow_succ', mul_nsmul, two_nsmul, nsmul_add]

theorem exists_uniform_stable_rank_two_model (b : ℕ) :
    ∃ C K : ℕ, 0 < C ∧ 0 < K ∧ ∀ (A : Finset ℤ) (L t k n r : ℕ),
      A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ) → 0 < t → L ≤ t * b → C ≤ 2 ^ t →
      C * 2 ^ (t + t) ≤ 2 ^ k → k + n ≤ L →
      2 * (6 * (L + 1) ^ 2 + 3) * r + 2 ≤ A.card →
      2 * 2 ^ freimanRank K * freimanTSizeFactor K 2 * (2 ^ L + 1) <
        (2 ^ (k + n)) ^ 2 * A.card →
      ∃ B ⊆ A, A.card ≤ B.card + (6 * (L + 1) ^ 2 + 3) * r ∧
        A.card ≤ 2 * B.card ∧ ∃ P : GeneralizedAP,
          P.rank ≤ 2 ∧ (∀ i, 0 < P.length i) ∧ P.TProper (2 ^ (k + n)) ∧
          (0 : ℤ) ∈ P.carrier ∧ insert 0 B ⊆ P.carrier ∧
          (P.dilate (2 ^ (k + n))).boxCard ≤
            freimanTSizeFactor K 2 * (dyadicSumsetWithZero B (k + n)).card ∧
          (∀ j < n, (dyadicSumsetWithZero B (k + (j + 1))).card ≤
            K * (dyadicSumsetWithZero B (k + j)).card) ∧
          ∀ D ⊆ B, B.card ≤ D.card + r → ∀ j ≤ n,
            2 * (dyadicSumsetWithZero B (k + j)).card <
              4 * (dyadicSumsetWithZero D (k + j)).card := by
  obtain ⟨C, K, hC, hK, hdouble⟩ := exists_uniform_highFold_doubling b
  refine ⟨C, K, hC, hK, ?_⟩
  intro A L t k n r hA ht hambient hscale hbase hwindow hcard hlarge
  obtain ⟨B, hBA, hcost, hstable⟩ := exists_subset_with_stable_dyadic_sumsets A L r hA
  have hBcard : 2 ≤ B.card := by nlinarith [hcost]
  have hhalf : A.card ≤ 2 * B.card := by nlinarith [hcost]
  have hBZ : insert 0 B ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ) := by
    apply Finset.insert_subset
    · simp
    · exact hBA.trans hA
  have hBZcard : 2 ≤ (insert 0 B).card := hBcard.trans (Finset.card_le_card (Finset.subset_insert _ _))
  have hN : 2 ^ L ≤ (2 ^ t) ^ b := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) hambient
  have hdouble' (j : ℕ) :
      ((2 ^ (k + j)) • insert 0 B + (2 ^ (k + j)) • insert 0 B).card ≤
        K * ((2 ^ (k + j)) • insert 0 B).card := by
    apply hdouble (insert 0 B) (2 ^ L) t hBZ (Finset.mem_insert_self _ _) hBZcard ht hN hscale
    exact hbase.trans (Nat.pow_le_pow_right (by omega) (Nat.le_add_right _ _))
  obtain ⟨P, hPrank, hpos, hproper, hzero, hBP, hmodel⟩ :=
    exists_noncollapsed_highFold_model_of_small_doubling (insert 0 B)
      (Finset.mem_insert_self _ _) (2 ^ (k + n)) K (by positivity) hK (hdouble' n)
  have hlarge' : 2 ^ freimanRank K * freimanTSizeFactor K 2 * (2 ^ L + 1) <
      (2 ^ (k + n)) ^ 2 * (insert 0 B).card := by
    have hsize : A.card ≤ 2 * (insert 0 B).card := hhalf.trans
      (Nat.mul_le_mul_left 2 (Finset.card_le_card (Finset.subset_insert _ _)))
    have hh := hlarge.trans_le (Nat.mul_le_mul_left ((2 ^ (k + n)) ^ 2) hsize)
    have hh' : 2 * (2 ^ freimanRank K * freimanTSizeFactor K 2 * (2 ^ L + 1)) <
        2 * ((2 ^ (k + n)) ^ 2 * (insert 0 B).card) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
    exact Nat.lt_of_mul_lt_mul_left hh'
  have hrank := P.rank_le_two_of_dense_highFold (insert 0 B) (2 ^ L) (2 ^ (k + n))
    (freimanTSizeFactor K 2) (freimanRank K) (by positivity) hpos hPrank hBP hBZ hmodel hlarge'
  refine ⟨B, hBA, hcost, hhalf, P, hrank, hpos, hproper, hzero, hBP, hmodel, ?_, ?_⟩
  · intro j hj
    rw [show k + (j + 1) = (k + j) + 1 by omega, dyadicSumsetWithZero_succ]
    exact hdouble' j
  · intro D hDB hremove j hj
    have hs := hstable D hDB hremove (k + j) (by omega)
    exact (Nat.mul_le_mul_right _ (by omega : 2 ≤ 3)).trans_lt hs

end Erdos587.CFP
