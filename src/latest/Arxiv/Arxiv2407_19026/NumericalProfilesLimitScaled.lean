import Arxiv.Arxiv2407_19026.NumericalProfilesLimitPolynomial
import Arxiv.Arxiv2407_19026.IntegerPowerPolynomial

/-!
# Scaled-integer model for the first-profile limit certificate

The degree-128 positivity certificates are checked over integer coefficient
lists.  This avoids repeatedly normalizing the same large rational
polynomials while retaining a direct semantic proof back to the definitions
used by the numerical profile.
-/

namespace Arxiv2407_19026

noncomputable section

open ScaledIntegerPower

def beta0LimitCertificateNat : List ℕ → ℕ
  | [] => 0
  | chunk :: chunks =>
      chunk * (10 ^ 18) ^ chunks.length +
        beta0LimitCertificateNat chunks

lemma beta0LimitCertificateNat_ne_zero
    (head : ℕ) (tail : List ℕ) (hhead : head ≠ 0) :
    beta0LimitCertificateNat (head :: tail) ≠ 0 := by
  rw [beta0LimitCertificateNat]
  have hpositive : 0 < head * (10 ^ 18) ^ tail.length := by
    positivity
  omega

def beta0LimitBernsteinValue :
    ℕ → List ℕ → ℝ → ℝ
  | _, [], _ => 0
  | 0, coefficient :: _, _ => coefficient
  | n + 1, coefficient :: coefficients, x =>
      coefficient * (1 - x) ^ (n + 1) +
        x * beta0LimitBernsteinValue n coefficients x

lemma beta0LimitBernsteinValue_nonneg
    (n : ℕ) (coefficients : List ℕ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ beta0LimitBernsteinValue n coefficients x := by
  induction n generalizing coefficients with
  | zero =>
      cases coefficients <;>
        simp [beta0LimitBernsteinValue]
  | succ n ih =>
      cases coefficients with
      | nil =>
          simp [beta0LimitBernsteinValue]
      | cons coefficient coefficients =>
          rw [beta0LimitBernsteinValue]
          exact add_nonneg
            (mul_nonneg (Nat.cast_nonneg _)
              (pow_nonneg (sub_nonneg.mpr hx.2) _))
            (mul_nonneg hx.1 (ih coefficients))

lemma evalIntegerPower_bernsteinValue
    (n : ℕ) (coefficients : List ℕ) (x : ℝ) :
    evalIntegerPower (integerPowerBernstein n coefficients) x =
      beta0LimitBernsteinValue n coefficients x := by
  induction n generalizing coefficients with
  | zero =>
      cases coefficients <;>
        norm_num [integerPowerBernstein,
          beta0LimitBernsteinValue, evalIntegerPower]
  | succ n ih =>
      cases coefficients with
      | nil =>
          simp [integerPowerBernstein,
            beta0LimitBernsteinValue, evalIntegerPower]
      | cons coefficient coefficients =>
          rw [integerPowerBernstein, evalIntegerPower_add,
            evalIntegerPower_scale,
            evalIntegerPower_oneSubPow,
            evalIntegerPower_shift, ih]
          norm_num [beta0LimitBernsteinValue]

lemma represents_integerScale (numerator : ℤ)
    {p : ScaledIntegerPower} {p' : RationalPowerPolynomial}
    (hp : Represents p p') :
    Represents (.scaleBy numerator 1 (by norm_num) p)
      (rationalPowerScale numerator p') := by
  simpa using represents_scaleBy numerator 1 (by norm_num) hp

def beta0LimitZScaled : ScaledIntegerPower :=
  .ofIntegers 1 [0, 1] (by norm_num)

def beta0LimitTaylorNineScaled : ScaledIntegerPower :=
  .ofIntegers 362880
    [362880, -362880, 181440, -60480, 15120,
      -3024, 504, -72, 9, -1]
    (by norm_num)

def beta0LimitErrorTenScaled : ScaledIntegerPower :=
  .ofIntegers 36288000
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11]
    (by norm_num)

def beta0LimitUScaled : ScaledIntegerPower :=
  .ofIntegers 1000000000000
    [1284524751404, -2131427997038, 2891286818537,
      -3264680122333, 3285022020636, -2940312871156,
      2192513219941, -1218022340257, 429628799767,
      -70285151867]
    (by norm_num)

def beta0LimitVScaled : ScaledIntegerPower :=
  .ofIntegers 1000000000000
    [2305025580120, -3251445731927, 2867372678585,
      -1452523072075, -29273824258, 722245058702,
      -585732339550, 214074650516, -26060252906,
      -2738794873]
    (by norm_num)

lemma beta0_limit_z_scaled_represents :
    Represents beta0LimitZScaled beta0LimitZPower := by
  intro x
  norm_num [beta0LimitZScaled, ScaledIntegerPower.eval,
    ScaledIntegerPower.ofIntegers, beta0LimitZPower,
    evalIntegerPower, rationalPowerEval]

lemma beta0_limit_taylor_nine_scaled_represents :
    Represents beta0LimitTaylorNineScaled
      beta0LimitTaylorNinePower := by
  intro x
  change evalIntegerPower
      [362880, -362880, 181440, -60480, 15120,
        -3024, 504, -72, 9, -1] x / 362880 =
    rationalPowerEval beta0LimitTaylorNinePower x
  norm_num [beta0LimitTaylorNinePower,
    evalIntegerPower, rationalPowerEval]
  ring_nf

lemma beta0_limit_error_ten_scaled_represents :
    Represents beta0LimitErrorTenScaled
      beta0LimitErrorTenPower := by
  intro x
  change evalIntegerPower
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11] x /
        36288000 = rationalPowerEval beta0LimitErrorTenPower x
  norm_num [beta0LimitErrorTenPower,
    evalIntegerPower, rationalPowerEval]
  ring_nf

lemma beta0_limit_u_scaled_represents :
    Represents beta0LimitUScaled beta0LimitUPower := by
  intro x
  change evalIntegerPower
      [1284524751404, -2131427997038, 2891286818537,
        -3264680122333, 3285022020636, -2940312871156,
        2192513219941, -1218022340257, 429628799767,
        -70285151867] x / 1000000000000 =
    rationalPowerEval beta0LimitUPower x
  norm_num [beta0LimitUPower, evalIntegerPower,
    rationalPowerEval]
  ring_nf

lemma beta0_limit_v_scaled_represents :
    Represents beta0LimitVScaled beta0LimitVPower := by
  intro x
  rw [beta0LimitVPower, rationalPowerEval_add,
    rationalPowerEval_scale, rationalPowerEval_pow]
  change evalIntegerPower
      [2305025580120, -3251445731927, 2867372678585,
        -1452523072075, -29273824258, 722245058702,
        -585732339550, 214074650516, -26060252906,
        -2738794873] x / 1000000000000 = _
  norm_num [evalIntegerPower, rationalPowerEval]
  ring_nf

def beta0LimitExpUpperScaled : ScaledIntegerPower :=
  .add beta0LimitTaylorNineScaled beta0LimitErrorTenScaled

def beta0LimitExpLowerScaled : ScaledIntegerPower :=
  .sub beta0LimitTaylorNineScaled beta0LimitErrorTenScaled

def beta0LimitQScaled : ScaledIntegerPower :=
  .mul beta0LimitZScaled beta0LimitUScaled

def beta0LimitBScaled : ScaledIntegerPower :=
  .sub (.constant 2 1 (by norm_num)) beta0LimitQScaled

def beta0LimitLogDenominatorScaled : ScaledIntegerPower :=
  .scaleBy 15 1 (by norm_num)
    (.mul (.pow beta0LimitBScaled 3)
      (.sub (.pow beta0LimitBScaled 2)
        (.pow beta0LimitQScaled 2)))

def beta0LimitLogNumeratorScaled : ScaledIntegerPower :=
  .scaleBy (-2) 1 (by norm_num)
    (.add
      (.add
        (.scaleBy 15 1 (by norm_num)
          (.mul
            (.mul beta0LimitQScaled
              (.pow beta0LimitBScaled 2))
            (.sub (.pow beta0LimitBScaled 2)
              (.pow beta0LimitQScaled 2))))
        (.scaleBy 5 1 (by norm_num)
          (.mul (.pow beta0LimitQScaled 3)
            (.sub (.pow beta0LimitBScaled 2)
              (.pow beta0LimitQScaled 2)))))
      (.scaleBy 3 1 (by norm_num)
        (.pow beta0LimitQScaled 5)))

def beta0LimitDLowerScaled : ScaledIntegerPower :=
  .mul beta0LimitZScaled
    (.sub beta0LimitVScaled beta0LimitExpUpperScaled)

def beta0LimitALowerScaled : ScaledIntegerPower :=
  .sub (.constant 1 1 (by norm_num))
    (.mul beta0LimitZScaled beta0LimitExpUpperScaled)

def beta0LimitAUpperScaled : ScaledIntegerPower :=
  .sub (.constant 1 1 (by norm_num))
    (.mul beta0LimitZScaled beta0LimitExpLowerScaled)

def beta0LimitSDenominatorScaled : ScaledIntegerPower :=
  .sub (.scaleBy 2 1 (by norm_num) beta0LimitAUpperScaled)
    beta0LimitDLowerScaled

def beta0LimitReserveDenominatorScaled : ScaledIntegerPower :=
  .scaleBy 105 1 (by norm_num)
    (.pow beta0LimitSDenominatorScaled 7)

def beta0LimitReserveNumeratorScaled : ScaledIntegerPower :=
  .scaleBy 2 1 (by norm_num)
    (.mul beta0LimitALowerScaled
      (.add
        (.add
          (.scaleBy 105 1 (by norm_num)
            (.mul beta0LimitDLowerScaled
              (.pow beta0LimitSDenominatorScaled 6)))
          (.scaleBy 35 1 (by norm_num)
            (.mul (.pow beta0LimitDLowerScaled 3)
              (.pow beta0LimitSDenominatorScaled 4))))
        (.add
          (.scaleBy 21 1 (by norm_num)
            (.mul (.pow beta0LimitDLowerScaled 5)
              (.pow beta0LimitSDenominatorScaled 2)))
          (.scaleBy 15 1 (by norm_num)
            (.pow beta0LimitDLowerScaled 7)))))

def beta0LimitNumeratorScaled : ScaledIntegerPower :=
  .add
    (.mul beta0LimitLogNumeratorScaled
      beta0LimitReserveDenominatorScaled)
    (.mul beta0LimitReserveNumeratorScaled
      beta0LimitLogDenominatorScaled)

def beta0LimitReserveScaled : ScaledIntegerPower :=
  .sub beta0LimitNumeratorScaled
    (.constant 1 1 (by norm_num))

lemma beta0_limit_reserve_scaled_represents :
    Represents beta0LimitReserveScaled beta0LimitReservePower := by
  have hexpUpper : Represents beta0LimitExpUpperScaled
      beta0LimitExpUpperPower :=
    represents_add beta0_limit_taylor_nine_scaled_represents
      beta0_limit_error_ten_scaled_represents
  have hexpLower : Represents beta0LimitExpLowerScaled
      beta0LimitExpLowerPower :=
    represents_sub beta0_limit_taylor_nine_scaled_represents
      beta0_limit_error_ten_scaled_represents
  have hq : Represents beta0LimitQScaled beta0LimitQPower :=
    represents_mul beta0_limit_z_scaled_represents
      beta0_limit_u_scaled_represents
  have htwo : Represents (.constant 2 1 (by norm_num))
      ([2] : RationalPowerPolynomial) := by
    intro x
    norm_num [ScaledIntegerPower.eval_constant, rationalPowerEval]
  have hone : Represents (.constant 1 1 (by norm_num))
      ([1] : RationalPowerPolynomial) := by
    intro x
    norm_num [ScaledIntegerPower.eval_constant, rationalPowerEval]
  have hb : Represents beta0LimitBScaled beta0LimitBPower := by
    rw [beta0LimitBPower]
    exact represents_sub htwo hq
  have hlogDen : Represents beta0LimitLogDenominatorScaled
      beta0LimitLogDenominatorPower := by
    rw [beta0LimitLogDenominatorPower]
    exact represents_integerScale 15
      (represents_mul (represents_pow hb 3)
        (represents_sub (represents_pow hb 2)
          (represents_pow hq 2)))
  have hlogNum : Represents beta0LimitLogNumeratorScaled
      beta0LimitLogNumeratorPower := by
    rw [beta0LimitLogNumeratorPower]
    exact represents_integerScale (-2)
      (represents_add
        (represents_add
          (represents_integerScale 15
            (represents_mul
              (represents_mul hq (represents_pow hb 2))
              (represents_sub (represents_pow hb 2)
                (represents_pow hq 2))))
          (represents_integerScale 5
            (represents_mul (represents_pow hq 3)
              (represents_sub (represents_pow hb 2)
                (represents_pow hq 2)))))
        (represents_integerScale 3
          (represents_pow hq 5)))
  have hd : Represents beta0LimitDLowerScaled
      beta0LimitDLowerPower := by
    rw [beta0LimitDLowerPower]
    exact represents_mul beta0_limit_z_scaled_represents
      (represents_sub beta0_limit_v_scaled_represents hexpUpper)
  have haLower : Represents beta0LimitALowerScaled
      beta0LimitALowerPower := by
    rw [beta0LimitALowerPower]
    exact represents_sub hone
      (represents_mul beta0_limit_z_scaled_represents hexpUpper)
  have haUpper : Represents beta0LimitAUpperScaled
      beta0LimitAUpperPower := by
    rw [beta0LimitAUpperPower]
    exact represents_sub hone
      (represents_mul beta0_limit_z_scaled_represents hexpLower)
  have hs : Represents beta0LimitSDenominatorScaled
      beta0LimitSDenominatorPower := by
    rw [beta0LimitSDenominatorPower]
    exact represents_sub
      (represents_integerScale 2 haUpper) hd
  have hreserveDen : Represents beta0LimitReserveDenominatorScaled
      beta0LimitReserveDenominatorPower := by
    rw [beta0LimitReserveDenominatorPower]
    exact represents_integerScale 105
      (represents_pow hs 7)
  have hreserveNum : Represents beta0LimitReserveNumeratorScaled
      beta0LimitReserveNumeratorPower := by
    rw [beta0LimitReserveNumeratorPower]
    exact represents_integerScale 2
      (represents_mul haLower
        (represents_add
          (represents_add
            (represents_integerScale 105
              (represents_mul hd (represents_pow hs 6)))
            (represents_integerScale 35
              (represents_mul (represents_pow hd 3)
                (represents_pow hs 4))))
          (represents_add
            (represents_integerScale 21
              (represents_mul (represents_pow hd 5)
                (represents_pow hs 2)))
            (represents_integerScale 15
              (represents_pow hd 7)))))
  have hnum : Represents beta0LimitNumeratorScaled
      beta0LimitNumeratorPower := by
    rw [beta0LimitNumeratorPower]
    exact represents_add
      (represents_mul hlogNum hreserveDen)
      (represents_mul hreserveNum hlogDen)
  rw [beta0LimitReservePower]
  exact represents_sub hnum hone

end

end Arxiv2407_19026
