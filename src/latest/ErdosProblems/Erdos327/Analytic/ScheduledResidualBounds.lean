import ErdosProblems.Erdos327.Analytic.SourceSmallBlocks
import ErdosProblems.Erdos327.Analytic.MixedSmallBlocks

/-!
# Elementary bounds for scheduled residual moments

These bounds are deliberately independent of Mertens estimates.  They
control transition and terminal blocks by observing that every summand is
between zero and one.
-/

namespace Erdos327.Analytic

open Finset

noncomputable section

/-- The exact source residual moment is at most the length of its interval. -/
theorem sourceDyadicResidualMoment_le_length
    (L X Y : ℕ) :
    sourceDyadicResidualMoment L X Y ≤ (Y : ℝ) := by
  unfold sourceDyadicResidualMoment
  calc
    (∑ d ∈ Icc 1 Y,
        if OddRough L d then
          (1 / 4 : ℝ) ^ primeFactorCountBetween L X d
        else 0) ≤
        ∑ _d ∈ Icc 1 Y, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      split_ifs
      · exact pow_le_one₀ (by norm_num) (by norm_num)
      · norm_num
    _ = Y := by simp

/-- The source residual moment vanishes at cutoff zero. -/
@[simp] theorem sourceDyadicResidualMoment_zero
    (L X : ℕ) :
    sourceDyadicResidualMoment L X 0 = 0 := by
  unfold sourceDyadicResidualMoment
  simp

/-- The exact mixed residual moment is at most the length of its interval
when both exponential bases exceed one. -/
theorem mixedExactResidualMoment_le_length
    (L N X : ℕ) {qb qo : ℝ}
    (hqb : 1 < qb) (hqo : 1 < qo) :
    mixedExactResidualMoment L N X qb qo ≤
      (N / (X * X) : ℕ) := by
  have hprod : 1 ≤ qb * qo := by
    nlinarith [mul_pos (sub_pos.mpr hqb) (sub_pos.mpr hqo)]
  have hprodPos : 0 < qb * qo :=
    mul_pos (by linarith) (by linarith)
  have hbase0 : 0 ≤ (1 / (qb * qo) : ℝ) := by positivity
  have hbase1 : (1 / (qb * qo) : ℝ) ≤ 1 :=
    (div_le_one₀ hprodPos).mpr hprod
  unfold mixedExactResidualMoment
  calc
    (∑ t ∈ Icc 1 (N / (X * X)),
        if Rough L t then
          (1 / (qb * qo)) ^ primeFactorCountBetween L X t
        else 0) ≤
        ∑ _t ∈ Icc 1 (N / (X * X)), (1 : ℝ) := by
      apply sum_le_sum
      intro t ht
      split_ifs
      · exact pow_le_one₀ hbase0 hbase1
      · norm_num
    _ = (N / (X * X) : ℕ) := by simp

/-- The mixed exact residual moment vanishes once its quotient cutoff is
zero. -/
theorem mixedExactResidualMoment_eq_zero_of_div_eq_zero
    {L N X : ℕ} {qb qo : ℝ}
    (hzero : N / (X * X) = 0) :
    mixedExactResidualMoment L N X qb qo = 0 := by
  unfold mixedExactResidualMoment
  rw [hzero]
  simp

end

end Erdos327.Analytic
