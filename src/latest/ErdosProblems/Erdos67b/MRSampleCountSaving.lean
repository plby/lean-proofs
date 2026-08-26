import ErdosProblems.Erdos67b.MRLastBlock

/-!
# Explicit threshold for the exceptional sample count

The subpower factor from the final block is bounded by an exponential
with the displayed finite threshold. No asymptotic estimate is assumed.
-/

namespace Erdos67b

noncomputable section

theorem mrLog_le_two_sqrt {R : ℝ} (hR : 1 ≤ R) : Real.log R ≤ 2 * Real.sqrt R := by
  have hR0 : 0 < R := by linarith
  have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hR0)
  rw [Real.log_sqrt hR0.le] at hh
  linarith

theorem mrNoSmallCountFactor_le_exponential {R : ℝ} (hR : 1 ≤ R) :
    mrNoSmallCountConstant * R ^ 3 * Real.exp (Real.sqrt R) ≤
      Real.exp (mrNoSmallCountConstant + 7 * Real.sqrt R) := by
  have hC : mrNoSmallCountConstant ≤ Real.exp mrNoSmallCountConstant := by
    linarith [Real.add_one_le_exp mrNoSmallCountConstant]
  have hR0 : 0 < R := by linarith
  have hpower : R ^ 3 ≤ Real.exp (6 * Real.sqrt R) := by
    calc
      _ = Real.exp (3 * Real.log R) := by
        rw [show (3 : ℝ) * Real.log R = (3 : ℕ) * Real.log R by norm_num,
          Real.exp_nat_mul, Real.exp_log hR0]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [mrLog_le_two_sqrt hR])
  calc
    _ ≤ Real.exp mrNoSmallCountConstant * Real.exp (6 * Real.sqrt R) * Real.exp (Real.sqrt R) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hC hpower (by positivity) (Real.exp_pos _).le)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem mrNoSmallCountFactor_le_small_power
    {eta R : ℝ} (heta : 0 < eta) (hR : 1 ≤ R)
    (hconstant : 8 * mrNoSmallCountConstant / eta ≤ R)
    (hsqrt : (56 / eta) ^ 2 ≤ R) :
    mrNoSmallCountConstant * R ^ 3 * Real.exp (Real.sqrt R) ≤ Real.exp (eta * R / 4) := by
  have hR0 : 0 ≤ R := by linarith
  have hs0 : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  have hs : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR0
  have hc : 8 * mrNoSmallCountConstant ≤ R * eta := (div_le_iff₀ heta).mp hconstant
  have hroot : 56 / eta ≤ Real.sqrt R := by nlinarith [div_pos (by norm_num : (0 : ℝ) < 56) heta]
  have hprod : 56 ≤ Real.sqrt R * eta := (div_le_iff₀ heta).mp hroot
  have hlin := mul_le_mul_of_nonneg_right hprod hs0
  apply (mrNoSmallCountFactor_le_exponential hR).trans
  apply Real.exp_le_exp.mpr
  nlinarith

theorem mrNoSmallOptimizedCountBudget_le_small_power
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J : ℕ} (hJ : 1 ≤ J) {T R : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hTR : Real.log T ≤ R) (hJR : mrLogScheduleUpper q₁ J ≤ Real.sqrt R)
    (hnext : Real.sqrt R ≤ mrLogScheduleUpper q₁ (J + 1))
    (hconstant : 8 * mrNoSmallCountConstant / eta ≤ R)
    (hsqrt : (56 / eta) ^ 2 ≤ R) :
    mrNoSmallOptimizedCountBudget eta p₁ q₁ J T ≤
      Real.exp (eta * R / 4) * Real.exp ((1 / 2 - eta) * Real.log T) := by
  exact (mrNoSmallOptimizedCountBudget_le_last_block heta0 heta1 hp hq hpq hlogq hbudget
    hJ hT hR hTR hJR hnext).trans (mul_le_mul_of_nonneg_right
      (mrNoSmallCountFactor_le_small_power heta0 hR hconstant hsqrt) (Real.exp_pos _).le)

theorem mrArithmetic_noSmall_sample_card_le_small_power
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J : ℕ} (hJ : 1 ≤ J) {R : ℝ} (hR : 1 ≤ R)
    (hJR : mrLogScheduleUpper q₁ J ≤ Real.sqrt R)
    (hnext : Real.sqrt R ≤ mrLogScheduleUpper q₁ (J + 1))
    (hconstant : 8 * mrNoSmallCountConstant / eta ≤ R)
    (hsqrt : (56 / eta) ^ 2 ≤ R)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) {T : ℝ} (hT : 1 ≤ T) (hTR : Real.log T ≤ R)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hU : ∀ t ∈ S, t ∈ mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J) :
    (S.card : ℝ) ≤ Real.exp (eta * R / 4) * Real.exp ((1 / 2 - eta) * Real.log T) := by
  have hcount := mrArithmetic_noSmall_sample_card_le_optimized heta0 heta1 hp hq hlogq hbudget
    hJ le_rfl hbound S hT hST hsep hU
  exact hcount.trans (mrNoSmallOptimizedCountBudget_le_small_power heta0 heta1 hp hq hpq hlogq hbudget
    hJ hT hR hTR hJR hnext hconstant hsqrt)

end

end Erdos67b
