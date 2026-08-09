import Arxiv.Arxiv2407_19026.NumericalProfilesLimitPolynomial

/-! Basic exact coefficient expansions for the limit certificate. -/

namespace Arxiv2407_19026

noncomputable section


def beta0LimitDecimalNat : List ℕ → ℕ
  | [] => 0
  | chunk :: chunks =>
      chunk * (10 ^ 18) ^ chunks.length +
        beta0LimitDecimalNat chunks

def beta0LimitQExpanded : RationalPowerPolynomial :=
  [
    0,
    ((321131187851 : ℚ) /
          250000000000),
    -((1065713998519 : ℚ) /
          500000000000),
    ((2891286818537 : ℚ) /
          1000000000000),
    -((3264680122333 : ℚ) /
          1000000000000),
    ((821255505159 : ℚ) /
          250000000000),
    -((735078217789 : ℚ) /
          250000000000),
    ((2192513219941 : ℚ) /
          1000000000000),
    -((1218022340257 : ℚ) /
          1000000000000),
    ((429628799767 : ℚ) /
          1000000000000),
    -((70285151867 : ℚ) /
          1000000000000)
  ]

def beta0LimitBExpanded : RationalPowerPolynomial :=
  [
    2,
    -((321131187851 : ℚ) /
          250000000000),
    ((1065713998519 : ℚ) /
          500000000000),
    -((2891286818537 : ℚ) /
          1000000000000),
    ((3264680122333 : ℚ) /
          1000000000000),
    -((821255505159 : ℚ) /
          250000000000),
    ((735078217789 : ℚ) /
          250000000000),
    -((2192513219941 : ℚ) /
          1000000000000),
    ((1218022340257 : ℚ) /
          1000000000000),
    -((429628799767 : ℚ) /
          1000000000000),
    ((70285151867 : ℚ) /
          1000000000000)
  ]

def beta0LimitDLowerExpanded : RationalPowerPolynomial :=
  [
    0,
    ((32625639503 : ℚ) /
          25000000000),
    -((2251445731927 : ℚ) /
          1000000000000),
    ((473474535717 : ℚ) /
          200000000000),
    -((154302768649 : ℚ) /
          120000000000),
    -((106410736387 : ℚ) /
          1500000000000),
    ((1095867588053 : ℚ) /
          1500000000000),
    -((105681821119 : ℚ) /
          180000000000),
    ((3374800745627 : ℚ) /
          15750000000000),
    -((821679216539 : ℚ) /
          31500000000000),
    -((1551334192991 : ℚ) /
          567000000000000),
    -((11 : ℚ) /
          36288000)
  ]

def beta0LimitALowerExpanded : RationalPowerPolynomial :=
  [
    1,
    -1,
    1,
    -((1 : ℚ) /
          2),
    ((1 : ℚ) /
          6),
    -((1 : ℚ) /
          24),
    ((1 : ℚ) /
          120),
    -((1 : ℚ) /
          720),
    ((1 : ℚ) /
          5040),
    -((1 : ℚ) /
          40320),
    ((1 : ℚ) /
          362880),
    -((11 : ℚ) /
          36288000)
  ]

def beta0LimitAUpperExpanded : RationalPowerPolynomial :=
  [
    1,
    -1,
    1,
    -((1 : ℚ) /
          2),
    ((1 : ℚ) /
          6),
    -((1 : ℚ) /
          24),
    ((1 : ℚ) /
          120),
    -((1 : ℚ) /
          720),
    ((1 : ℚ) /
          5040),
    -((1 : ℚ) /
          40320),
    ((1 : ℚ) /
          362880),
    ((11 : ℚ) /
          36288000)
  ]

def beta0LimitSDenominatorExpanded : RationalPowerPolynomial :=
  [
    2,
    -((82625639503 : ℚ) /
          25000000000),
    ((4251445731927 : ℚ) /
          1000000000000),
    -((673474535717 : ℚ) /
          200000000000),
    ((194302768649 : ℚ) /
          120000000000),
    -((18589263613 : ℚ) /
          1500000000000),
    -((1070867588053 : ℚ) /
          1500000000000),
    ((105181821119 : ℚ) /
          180000000000),
    -((3368550745627 : ℚ) /
          15750000000000),
    ((820116716539 : ℚ) /
          31500000000000),
    ((1554459192991 : ℚ) /
          567000000000000),
    ((11 : ℚ) /
          12096000)
  ]

lemma beta0_limit_q_expansion :
    beta0LimitQPower = beta0LimitQExpanded := by
  norm_num [beta0LimitQPower, beta0LimitZPower,
    beta0LimitUPower, beta0LimitQExpanded,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

lemma beta0_limit_b_expansion :
    beta0LimitBPower = beta0LimitBExpanded := by
  rw [beta0LimitBPower, beta0_limit_q_expansion]
  norm_num [beta0LimitBExpanded, beta0LimitQExpanded,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd,
    beta0LimitDecimalNat]

lemma beta0_limit_d_lower_expansion :
    beta0LimitDLowerPower = beta0LimitDLowerExpanded := by
  norm_num [beta0LimitDLowerPower, beta0LimitZPower,
    beta0LimitVPower, beta0LimitExpUpperPower,
    beta0LimitTaylorNinePower, beta0LimitErrorTenPower,
    beta0LimitDLowerExpanded, rationalPowerPow,
    rationalPowerMul, rationalPowerSub, rationalPowerNeg,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

lemma beta0_limit_a_lower_expansion :
    beta0LimitALowerPower = beta0LimitALowerExpanded := by
  norm_num [beta0LimitALowerPower, beta0LimitZPower,
    beta0LimitExpUpperPower, beta0LimitTaylorNinePower,
    beta0LimitErrorTenPower, beta0LimitALowerExpanded,
    rationalPowerMul, rationalPowerSub, rationalPowerNeg,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

lemma beta0_limit_a_upper_expansion :
    beta0LimitAUpperPower = beta0LimitAUpperExpanded := by
  norm_num [beta0LimitAUpperPower, beta0LimitZPower,
    beta0LimitExpLowerPower, beta0LimitTaylorNinePower,
    beta0LimitErrorTenPower, beta0LimitAUpperExpanded,
    rationalPowerMul, rationalPowerSub, rationalPowerNeg,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

lemma beta0_limit_s_denominator_expansion :
    beta0LimitSDenominatorPower =
      beta0LimitSDenominatorExpanded := by
  rw [beta0LimitSDenominatorPower,
    beta0_limit_a_upper_expansion,
    beta0_limit_d_lower_expansion]
  norm_num [beta0LimitAUpperExpanded,
    beta0LimitDLowerExpanded,
    beta0LimitSDenominatorExpanded,
    rationalPowerSub, rationalPowerNeg,
    rationalPowerAdd, rationalPowerScale,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
