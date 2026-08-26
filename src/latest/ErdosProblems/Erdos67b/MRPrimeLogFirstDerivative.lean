import ErdosProblems.Erdos67b.MRPrimeWeylDecay

/-! # The first-derivative range of the prime logarithmic kernel -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

open Erdos1149 LogPhaseHigherDerivative ResidueLogPhase
open LogPhaseSum LSeriesLogPhaseBridge

theorem mrNorm_positiveLogBlock_le_firstDerivative
    {a U : ℝ} {L : ℕ} (ha : 0 < a) (hU : 0 < U)
    (haU : a ≤ U / 2) (hwindow : (L : ℝ) + 1 ≤ 2 * U) :
    ‖∑ j ∈ Finset.range L, HigherDerivative.phase (shiftedLogPhase a U j)‖ ≤
      3 * U / a := by
  let lam : ℝ := a / (3 * U)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlamSmall : lam ≤ 1 / 6 := by
    dsimp [lam]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * U)).2
    linarith
  have hcond := terminalIncrementCondition_shiftedLog
    (a := a) (X := U) (lam := lam) (s := 0) (K := 1) (d := 1) (P := L)
    ha hU (by norm_num) []
    (by simp [HigherDerivative.constantControlledSteps,
      RestrictedWeyl.offDiagonalHistoryLeaves])
    (by simpa using hwindow)
    (by simp [lam, zpow_neg, div_eq_mul_inv])
    (by
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul,
        Nat.reduceAdd, zpow_neg, zpow_one]
      have hh : a / U ≤ 1 / 2 := (div_le_iff₀ hU).2 (by linarith)
      rw [← div_eq_mul_inv]
      linarith)
  have hb := HigherDerivative.norm_phaseSum_le_inv_of_terminalIncrementCondition
    (fun j ↦ shiftedLogPhase a U j) L lam hlam (by linarith)
    (by simpa only [HigherDerivative.iteratedPairDifference] using hcond)
  convert hb using 1
  dsimp [lam]
  field_simp

theorem mrNorm_positiveLogBlock_le_firstDerivative_add_one
    {a U : ℝ} {L : ℕ} (ha : 0 < a) (hU : 1 ≤ U)
    (haU : a ≤ U / 2) (hL : (L : ℝ) ≤ U + 1) :
    ‖∑ j ∈ Finset.range L, HigherDerivative.phase (shiftedLogPhase a U j)‖ ≤
      3 * U / a + 1 := by
  cases L with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, norm_zero]; positivity
  | succ L =>
      have hb := mrNorm_positiveLogBlock_le_firstDerivative (L := L) ha
        (by linarith : 0 < U) haU (by push_cast at hL; linarith)
      rw [Finset.sum_range_succ]
      exact (norm_add_le _ _).trans (by simpa using add_le_add_right hb 1)

theorem mrNorm_primeMellin_Icc_eq_positiveLogBlock
    {A M : ℕ} (hA : 0 < A) (hAM : A ≤ M) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc A M, mrPrimeMellinMonomial 0 t n‖ =
      ‖∑ j ∈ Finset.range (M - A + 1),
        HigherDerivative.phase (shiftedLogPhase (positiveLogCoefficient t) A j)‖ := by
  have hh := norm_residueClassSum_natLogTwist_eq_positiveShifted
    (A := A) (M := M) (0 : ZMod 1) (-t) hA
  simp only [residueClassSum, Subsingleton.elim (_ : ZMod 1) 0,
    Finset.filter_true, residueIntervalLength, mrFirstResidueAtOrAbove_mod_one,
    if_pos hAM, Nat.div_one, Nat.cast_one, div_one] at hh
  simp_rw [mrPrimeMellinMonomial_zero_eq_natLogTwist]
  simpa only [positiveLogCoefficient, abs_neg] using hh

theorem mrNorm_primeMellin_dyadic_le_firstDerivative
    {A M : ℕ} (hA : 1 ≤ A) (hM : M ≤ 2 * A)
    {t : ℝ} (ht : t ≠ 0) (haU : positiveLogCoefficient t ≤ (A : ℝ) / 2) :
    ‖∑ n ∈ Finset.Icc A M, mrPrimeMellinMonomial 0 t n‖ ≤
      3 * (A : ℝ) / positiveLogCoefficient t + 1 := by
  by_cases hAM : A ≤ M
  · rw [mrNorm_primeMellin_Icc_eq_positiveLogBlock (by omega) hAM]
    apply mrNorm_positiveLogBlock_le_firstDerivative_add_one
      (positiveLogCoefficient_pos ht) (by exact_mod_cast hA) haU
    have hh : M - A + 1 ≤ A + 1 := by omega
    exact_mod_cast hh
  · simp only [Finset.Icc_eq_empty_of_lt (by omega : M < A),
      Finset.sum_empty, norm_zero]
    have := positiveLogCoefficient_pos ht
    positivity

end

end Erdos67b
