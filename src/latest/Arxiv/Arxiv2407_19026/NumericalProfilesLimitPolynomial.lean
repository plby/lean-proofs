import Arxiv.Arxiv2407_19026.NumericalProfilesLimitBounds
import Util.RationalPowerPolynomial

/-!
# Power-polynomial model for the first-profile limit bound

The rational numerator used for the limit estimate is represented by an
exact coefficient list.  This lets later modules check its interval
certificates by coefficient arithmetic instead of a large symbolic `ring`
calculation.
-/

namespace Arxiv2407_19026

noncomputable section

def beta0LimitZPower : RationalPowerPolynomial :=
  [0, 1]

def beta0LimitTaylorNinePower : RationalPowerPolynomial :=
  [1, -1, 1 / 2, -1 / 6, 1 / 24, -1 / 120,
    1 / 720, -1 / 5040, 1 / 40320, -1 / 362880]

def beta0LimitErrorTenPower : RationalPowerPolynomial :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11 / 36288000]

def beta0LimitUPower : RationalPowerPolynomial :=
  [1.284024751404 + 1 / 2000,
    -2.131427997038, 2.891286818537,
    -3.264680122333, 3.285022020636,
    -2.940312871156, 2.192513219941,
    -1.218022340257, 0.429628799767,
    -0.070285151867]

def beta0LimitVPower : RationalPowerPolynomial :=
  rationalPowerAdd
    [2.284025580120 + 1 / 1000,
      -3.131445731927, 2.567372678585,
      -1.052523072075, -0.329273824258,
      0.842245058702, -0.605732339550,
      0.214074650516, -0.026060252906,
      -0.002738794873]
    (rationalPowerScale (1 / 50)
      (rationalPowerPow [1, -1] 6))

def beta0LimitExpUpperPower : RationalPowerPolynomial :=
  rationalPowerAdd beta0LimitTaylorNinePower
    beta0LimitErrorTenPower

def beta0LimitExpLowerPower : RationalPowerPolynomial :=
  rationalPowerSub beta0LimitTaylorNinePower
    beta0LimitErrorTenPower

def beta0LimitQPower : RationalPowerPolynomial :=
  rationalPowerMul beta0LimitZPower beta0LimitUPower

def beta0LimitBPower : RationalPowerPolynomial :=
  rationalPowerSub [2] beta0LimitQPower

def beta0LimitLogDenominatorPower : RationalPowerPolynomial :=
  rationalPowerScale 15
    (rationalPowerMul
      (rationalPowerPow beta0LimitBPower 3)
      (rationalPowerSub
        (rationalPowerPow beta0LimitBPower 2)
        (rationalPowerPow beta0LimitQPower 2)))

def beta0LimitLogNumeratorPower : RationalPowerPolynomial :=
  rationalPowerScale (-2)
    (rationalPowerAdd
      (rationalPowerAdd
        (rationalPowerScale 15
          (rationalPowerMul
            (rationalPowerMul beta0LimitQPower
              (rationalPowerPow beta0LimitBPower 2))
            (rationalPowerSub
              (rationalPowerPow beta0LimitBPower 2)
              (rationalPowerPow beta0LimitQPower 2))))
        (rationalPowerScale 5
          (rationalPowerMul
            (rationalPowerPow beta0LimitQPower 3)
            (rationalPowerSub
              (rationalPowerPow beta0LimitBPower 2)
              (rationalPowerPow beta0LimitQPower 2)))))
      (rationalPowerScale 3
        (rationalPowerPow beta0LimitQPower 5)))

def beta0LimitDLowerPower : RationalPowerPolynomial :=
  rationalPowerMul beta0LimitZPower
    (rationalPowerSub beta0LimitVPower
      beta0LimitExpUpperPower)

def beta0LimitALowerPower : RationalPowerPolynomial :=
  rationalPowerSub [1]
    (rationalPowerMul beta0LimitZPower
      beta0LimitExpUpperPower)

def beta0LimitAUpperPower : RationalPowerPolynomial :=
  rationalPowerSub [1]
    (rationalPowerMul beta0LimitZPower
      beta0LimitExpLowerPower)

def beta0LimitSDenominatorPower : RationalPowerPolynomial :=
  rationalPowerSub
    (rationalPowerScale 2 beta0LimitAUpperPower)
    beta0LimitDLowerPower

def beta0LimitReserveDenominatorPower : RationalPowerPolynomial :=
  rationalPowerScale 105
    (rationalPowerPow beta0LimitSDenominatorPower 7)

def beta0LimitReserveNumeratorPower : RationalPowerPolynomial :=
  rationalPowerScale 2
    (rationalPowerMul beta0LimitALowerPower
      (rationalPowerAdd
        (rationalPowerAdd
          (rationalPowerScale 105
            (rationalPowerMul beta0LimitDLowerPower
              (rationalPowerPow
                beta0LimitSDenominatorPower 6)))
          (rationalPowerScale 35
            (rationalPowerMul
              (rationalPowerPow beta0LimitDLowerPower 3)
              (rationalPowerPow
                beta0LimitSDenominatorPower 4))))
        (rationalPowerAdd
          (rationalPowerScale 21
            (rationalPowerMul
              (rationalPowerPow beta0LimitDLowerPower 5)
              (rationalPowerPow
                beta0LimitSDenominatorPower 2)))
          (rationalPowerScale 15
            (rationalPowerPow beta0LimitDLowerPower 7)))))

def beta0LimitNumeratorPower : RationalPowerPolynomial :=
  rationalPowerAdd
    (rationalPowerMul beta0LimitLogNumeratorPower
      beta0LimitReserveDenominatorPower)
    (rationalPowerMul beta0LimitReserveNumeratorPower
      beta0LimitLogDenominatorPower)

def beta0LimitReservePower : RationalPowerPolynomial :=
  rationalPowerSub beta0LimitNumeratorPower [1]

lemma beta0_limit_u_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitUPower z = beta0U z := by
  norm_num [beta0LimitUPower, rationalPowerEval, beta0U]
  ring

lemma beta0_limit_v_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitVPower z = beta0VLarge z := by
  rw [beta0LimitVPower, rationalPowerEval_add,
    rationalPowerEval_scale, rationalPowerEval_pow]
  norm_num [rationalPowerEval, beta0VLarge]
  ring

lemma beta0_limit_taylor_nine_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitTaylorNinePower z =
      KernelBounds.expNegTaylor9 z := by
  norm_num [beta0LimitTaylorNinePower, rationalPowerEval,
    KernelBounds.expNegTaylor9]
  ring

lemma beta0_limit_error_ten_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitErrorTenPower z =
      KernelBounds.expNegError10 z := by
  norm_num [beta0LimitErrorTenPower, rationalPowerEval,
    KernelBounds.expNegError10, Nat.factorial]
  ring

lemma beta0_limit_exp_upper_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitExpUpperPower z =
      expNegUpper z := by
  rw [beta0LimitExpUpperPower, rationalPowerEval_add,
    beta0_limit_taylor_nine_power_eval,
    beta0_limit_error_ten_power_eval]
  rfl

lemma beta0_limit_exp_lower_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitExpLowerPower z =
      beta0LimitExpLower z := by
  rw [beta0LimitExpLowerPower, rationalPowerEval_sub,
    beta0_limit_taylor_nine_power_eval,
    beta0_limit_error_ten_power_eval]
  rfl

lemma beta0_limit_q_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitQPower z = beta0LimitQ z := by
  rw [beta0LimitQPower, rationalPowerEval_mul,
    beta0_limit_u_power_eval]
  norm_num [beta0LimitZPower, rationalPowerEval,
    beta0LimitQ]

lemma beta0_limit_b_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitBPower z = beta0LimitB z := by
  rw [beta0LimitBPower, rationalPowerEval_sub,
    beta0_limit_q_power_eval]
  norm_num [rationalPowerEval, beta0LimitB]

lemma beta0_limit_log_denominator_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitLogDenominatorPower z =
      beta0LimitLogDenominator z := by
  simp only [beta0LimitLogDenominatorPower,
    rationalPowerEval_scale, rationalPowerEval_mul,
    rationalPowerEval_pow, rationalPowerEval_sub,
    beta0_limit_b_power_eval, beta0_limit_q_power_eval]
  norm_num [beta0LimitLogDenominator]
  ring

lemma beta0_limit_log_numerator_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitLogNumeratorPower z =
      beta0LimitLogNumerator z := by
  simp only [beta0LimitLogNumeratorPower,
    rationalPowerEval_scale, rationalPowerEval_add,
    rationalPowerEval_mul, rationalPowerEval_pow,
    rationalPowerEval_sub, beta0_limit_b_power_eval,
    beta0_limit_q_power_eval]
  norm_num [beta0LimitLogNumerator]
  ring

lemma beta0_limit_d_lower_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitDLowerPower z =
      beta0LimitDLower z := by
  rw [beta0LimitDLowerPower, rationalPowerEval_mul,
    rationalPowerEval_sub, beta0_limit_v_power_eval,
    beta0_limit_exp_upper_power_eval]
  norm_num [beta0LimitZPower, rationalPowerEval,
    beta0LimitDLower]

lemma beta0_limit_a_lower_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitALowerPower z =
      beta0LimitALower z := by
  rw [beta0LimitALowerPower, rationalPowerEval_sub,
    rationalPowerEval_mul,
    beta0_limit_exp_upper_power_eval]
  norm_num [beta0LimitZPower, rationalPowerEval,
    beta0LimitALower]

lemma beta0_limit_a_upper_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitAUpperPower z =
      beta0LimitAUpper z := by
  rw [beta0LimitAUpperPower, rationalPowerEval_sub,
    rationalPowerEval_mul,
    beta0_limit_exp_lower_power_eval]
  norm_num [beta0LimitZPower, rationalPowerEval,
    beta0LimitAUpper]

lemma beta0_limit_s_denominator_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitSDenominatorPower z =
      beta0LimitSDenominator z := by
  rw [beta0LimitSDenominatorPower, rationalPowerEval_sub,
    rationalPowerEval_scale, beta0_limit_a_upper_power_eval,
    beta0_limit_d_lower_power_eval]
  rfl

lemma beta0_limit_reserve_denominator_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitReserveDenominatorPower z =
      beta0LimitReserveDenominator z := by
  rw [beta0LimitReserveDenominatorPower,
    rationalPowerEval_scale, rationalPowerEval_pow,
    beta0_limit_s_denominator_power_eval]
  rfl

lemma beta0_limit_reserve_numerator_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitReserveNumeratorPower z =
      beta0LimitReserveNumerator z := by
  simp only [beta0LimitReserveNumeratorPower,
    rationalPowerEval_scale, rationalPowerEval_mul,
    rationalPowerEval_add, rationalPowerEval_pow,
    beta0_limit_a_lower_power_eval,
    beta0_limit_d_lower_power_eval,
    beta0_limit_s_denominator_power_eval]
  norm_num [beta0LimitReserveNumerator]
  ring

lemma beta0_limit_numerator_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitNumeratorPower z =
      beta0LimitNumerator z := by
  simp only [beta0LimitNumeratorPower, rationalPowerEval_add,
    rationalPowerEval_mul,
    beta0_limit_log_numerator_power_eval,
    beta0_limit_reserve_denominator_power_eval,
    beta0_limit_reserve_numerator_power_eval,
    beta0_limit_log_denominator_power_eval]
  rfl

lemma beta0_limit_reserve_power_eval (z : ℝ) :
    rationalPowerEval beta0LimitReservePower z =
      beta0LimitNumerator z - 1 := by
  rw [beta0LimitReservePower, rationalPowerEval_sub,
    beta0_limit_numerator_power_eval]
  norm_num [rationalPowerEval]

end

end Arxiv2407_19026
