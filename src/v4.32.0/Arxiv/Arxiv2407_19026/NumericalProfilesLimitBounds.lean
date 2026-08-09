import Arxiv.Arxiv2407_19026.NumericalProfilesKernelBounds
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.PLower
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.ULower

/-!
# Semantic reduction of the first-profile limit inequality

The affine-grid check for the limit inequality is replaced by logarithm and
exponential bounds whose remaining numerical obligation is a rational
polynomial.
-/

namespace Arxiv2407_19026

noncomputable section

def beta0LimitExpLower (z : ℝ) : ℝ :=
  KernelBounds.expNegTaylor9 z - KernelBounds.expNegError10 z

def beta0LimitQ (z : ℝ) : ℝ :=
  z * beta0U z

def beta0LimitB (z : ℝ) : ℝ :=
  2 - beta0LimitQ z

def beta0LimitLogDenominator (z : ℝ) : ℝ :=
  15 * beta0LimitB z ^ 3 *
    (beta0LimitB z ^ 2 - beta0LimitQ z ^ 2)

def beta0LimitLogNumerator (z : ℝ) : ℝ :=
  -2 *
    (15 * beta0LimitQ z * beta0LimitB z ^ 2 *
        (beta0LimitB z ^ 2 - beta0LimitQ z ^ 2) +
      5 * beta0LimitQ z ^ 3 *
        (beta0LimitB z ^ 2 - beta0LimitQ z ^ 2) +
      3 * beta0LimitQ z ^ 5)

def beta0LimitDLower (z : ℝ) : ℝ :=
  z * (beta0VLarge z - expNegUpper z)

def beta0LimitALower (z : ℝ) : ℝ :=
  1 - z * expNegUpper z

def beta0LimitAUpper (z : ℝ) : ℝ :=
  1 - z * beta0LimitExpLower z

def beta0LimitSDenominator (z : ℝ) : ℝ :=
  2 * beta0LimitAUpper z - beta0LimitDLower z

def beta0LimitReserveDenominator (z : ℝ) : ℝ :=
  105 * beta0LimitSDenominator z ^ 7

def beta0LimitReserveNumerator (z : ℝ) : ℝ :=
  2 * beta0LimitALower z *
    (105 * beta0LimitDLower z *
        beta0LimitSDenominator z ^ 6 +
      35 * beta0LimitDLower z ^ 3 *
        beta0LimitSDenominator z ^ 4 +
      21 * beta0LimitDLower z ^ 5 *
        beta0LimitSDenominator z ^ 2 +
      15 * beta0LimitDLower z ^ 7)

def beta0LimitNumerator (z : ℝ) : ℝ :=
  beta0LimitLogNumerator z *
      beta0LimitReserveDenominator z +
    beta0LimitReserveNumerator z *
      beta0LimitLogDenominator z

def beta0LimitDenominator (z : ℝ) : ℝ :=
  beta0LimitLogDenominator z *
    beta0LimitReserveDenominator z

end

end Arxiv2407_19026
